//! The expression and type lowering, over the lowering's base and its
//! families. Each body reads the lowering through its host, `F: Families`.

mod access;
mod arity;
pub mod boundary;
mod capability;
pub mod conditional;
pub mod description;
pub mod entry;
mod exits;
pub mod functor;
pub mod generic;
mod identity;
pub mod implicit;
pub mod inert;
mod loops;
mod method;
mod model;
mod native;
pub mod natural;
pub mod opening;
pub mod patched;
pub mod path;
pub mod phase;
pub mod reader;
pub mod sealing;
mod session;
pub mod splice;
pub mod staged;
pub mod ua;
pub mod world;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::btree_map::Entry;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::OnceCell;
use core::ops::ControlFlow;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::identity::Relation;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::WorldForm;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_lowering_base::lower::Block;
use gandr_surface_lowering_base::lower::Body;
use gandr_surface_lowering_base::lower::Bridge;
use gandr_surface_lowering_base::lower::Carrier;
use gandr_surface_lowering_base::lower::Code;
use gandr_surface_lowering_base::lower::Context;
use gandr_surface_lowering_base::lower::Current;
use gandr_surface_lowering_base::lower::Function;
use gandr_surface_lowering_base::lower::InPayload;
use gandr_surface_lowering_base::lower::InstanceType;
use gandr_surface_lowering_base::lower::LabelRead;
use gandr_surface_lowering_base::lower::LabelSite;
use gandr_surface_lowering_base::lower::Listed;
use gandr_surface_lowering_base::lower::Lowered;
use gandr_surface_lowering_base::lower::MODEL;
use gandr_surface_lowering_base::lower::Parameter;
use gandr_surface_lowering_base::lower::Plan;
use gandr_surface_lowering_base::lower::Produced;
use gandr_surface_lowering_base::lower::Reading;
use gandr_surface_lowering_base::lower::Relating;
use gandr_surface_lowering_base::lower::Resolved;
use gandr_surface_lowering_base::lower::Sink;
use gandr_surface_lowering_base::lower::Site;
use gandr_surface_lowering_base::lower::Statement;
use gandr_surface_lowering_base::lower::StatementBinding;
use gandr_surface_lowering_base::lower::Stretch;
use gandr_surface_lowering_base::lower::Taking;
use gandr_surface_lowering_base::lower::TextSegment;
use gandr_surface_lowering_base::lower::arguments;
use gandr_surface_lowering_base::lower::classified;
use gandr_surface_lowering_base::lower::closed;
use gandr_surface_lowering_base::lower::context::extend_sources;
use gandr_surface_lowering_base::lower::context::own_positions;
use gandr_surface_lowering_base::lower::delimited;
use gandr_surface_lowering_base::lower::delimited_list;
use gandr_surface_lowering_base::lower::exactly;
use gandr_surface_lowering_base::lower::exhausted;
use gandr_surface_lowering_base::lower::exits::Exit;
use gandr_surface_lowering_base::lower::families::Families;
use gandr_surface_lowering_base::lower::literal;
use gandr_surface_lowering_base::lower::lowered;
use gandr_surface_lowering_base::lower::multiplicity_one;
use gandr_surface_lowering_base::lower::named;
use gandr_surface_lowering_base::lower::parse_literal;
use gandr_surface_lowering_base::lower::recursion;
use gandr_surface_lowering_base::lower::runs::NestedSite;
use gandr_surface_lowering_base::lower::scoped;
use gandr_surface_lowering_base::lower::stated;
use gandr_surface_lowering_base::lower::stretch;
use gandr_surface_lowering_base::lower::unread_pattern;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::FormRank;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeEntry;
use crate::attribute::AttributeRegistry;
use crate::attribute::AttributeSchema;
use crate::attribute::AttributeTable;
use crate::attribute::PayloadForm;
use crate::attribute::PayloadVerdict;
use crate::attribute::RegisteredAttribute;
use crate::attribute::deprecation;
use crate::attribute::members;
use crate::attribute::names;
use crate::attribute::payload;
use crate::attribute::payload_form;
use crate::attribute::payload_verdict;
use crate::attribute::texts;
use crate::by_form::At;
use crate::by_form::ByForm;
use crate::by_form::FormStretch;
use crate::classify::FailureClass;
use crate::coincide::Decisions;
use crate::doc::Documentation;
use crate::doc::INNER_DOC_LINE;
use crate::doc::LinkCount;
use crate::doc::LinkTarget;
use crate::doc::read_doc;
use crate::error::CrossedExit;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::error::MatchFault;
use crate::error::Unexported;
use crate::form::Cursor;
use crate::form::Family;
use crate::form::FormName;
use crate::form::Former;
use crate::form::KeywordOpening;
use crate::form::Misspelt;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Repair;
use crate::form::Run;
use crate::form::RunReading;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::Universe;
use crate::form::applied_word;
use crate::form::bare_bracket;
use crate::form::family_of;
use crate::form::misspelt_keyword;
use crate::form::misspelt_operator;
use crate::form::opens_expression;
use crate::form::read_as_type;
use crate::form::read_pieces;
use crate::form::run_reading;
use crate::form::shape_of;
use crate::form::tile_label;
use crate::import::ImportResolution;
use crate::import::ImportSignature;
use crate::import::Opening;
use crate::import::Translation;
use crate::layout::bracket_form;
use crate::layout::misplaced;
use crate::lower::capability::Capability;
use crate::lower::capability::CapabilityRef;
use crate::lower::exits::Exits;
use crate::lower::exits::ExitsRef;
use crate::lower::identity::Identities;
use crate::lower::identity::IdentitiesRef;
use crate::lower::model::Models;
use crate::lower::model::ModelsRef;
use crate::lower::native::Native;
use crate::lower::native::NativeRef;
use crate::module::BodyScope;
use crate::module::Collected;
use crate::module::Constructor;
use crate::module::Container;
use crate::module::DeclarationOutcome;
use crate::module::DeclarationParts;
use crate::module::DeclarationSlot;
use crate::module::DecoratedModule;
use crate::module::Functor;
use crate::module::Generators;
use crate::module::Half;
use crate::module::HalfAt;
use crate::module::Halves;
use crate::module::KeyedTables;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::module::LoweredStructure;
use crate::module::ManifestComponent;
use crate::module::Member;
use crate::module::Operand;
use crate::module::ParameterForm;
use crate::module::Payload;
use crate::module::ReceiverMode;
use crate::module::SealedComponent;
use crate::module::SlotIndex;
use crate::module::Stratum;
use crate::module::StructureIndex;
use crate::module::TERMS;
use crate::module::THEORY_CODE;
use crate::module::TypeComponent;
use crate::module::TypeMeaning;
use crate::module::ValueComponent;
use crate::module::WrittenAttribute;
use crate::module::WrittenDoc;
use crate::module::collect_source;
use crate::module::declaration_half;
use crate::module::manifest_type;
use crate::module::slot_refusal;
use crate::namespace::Binding;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::RecognitionSite;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::namespace::Trie;
use crate::origin::ChannelName;
use crate::origin::ComponentName;
use crate::origin::Insertion;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Omitted;
use crate::origin::Origin;
use crate::origin::OriginTable;
use crate::origin::Provenance;
use crate::origin::SplitComponent;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::Mentioned;
use crate::resolve::OperandCount;
use crate::resolve::ScopeId;
use crate::resolve::Shadow;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::resolve::homed_atom;
use crate::resolve::homed_former;
use crate::resolve::type_atom;
use crate::resolve::type_head;
use crate::slot::Role;
use crate::slot::Visibility;
use crate::unbuilt::Unbuilt;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitKey;
use crate::written_import::decode_escapes;

/// How a form standing where a body ends treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants partition what a form does at a body's end.
/// - provides: the vocabulary of exit inference.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit, a match passing its end to its arms and a
///   returner ending a body distinguish the three.
/// - witness: `gandr-surface-lowering::lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Ending
{
    /// The form is the exit: `return` or `become`, or a loop's `break` or
    /// `continue`.
    Exit,
    /// The form passes the end on to what ends it — a block's last
    /// computation, a match's arms, a grouping's operand, a lambda's own body,
    /// which answers the function type the end has, a loop's `break`s — or is
    /// a hole, which the author has yet to fill.
    Passes,
    /// The form ends the body without an exit, so the lowering infers the one
    /// its position names: at a body's end, `return` over a value and `become`
    /// over a computation; at a loop body's end, the loop's re-entry.
    Inferred,
}

/// How `former`, standing where a body ends, treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `return`, `become`, `break` and `continue` are the exit; a block,
///   a match, an offer, a copattern block, a grouping, a lambda, a loop and a
///   hole pass the end on; every other former takes an inferred exit.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exits settle, a match ending in exits settles, and a
///   returner or a call ending a body takes an inferred exit at itself.
/// - witness: `gandr-surface-lowering::lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
/// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[spec(ensures: |ret| match former {
    Former::Exit | Former::Become | Former::Break | Former::Continue => ret == Ending::Exit,
    Former::Block | Former::Case | Former::If | Former::Offer | Former::LazyRecord | Former::Parenthesized | Former::Lambda | Former::Hole | Former::Loop | Former::While | Former::For => ret == Ending::Passes,
    Former::Name | Former::Constructor | Former::Number | Former::Boolean | Former::Text | Former::Character | Former::TypeQuote | Former::Thunk | Former::Return | Former::Force | Former::Run | Former::Call | Former::ForgetModel | Former::Telescope | Former::List | Former::PackModel | Former::Injection | Former::Binary | Former::Unary | Former::Projection | Former::TypeHead | Former::TypePath | Former::Universe | Former::TypeApplication | Former::ThunkType | Former::ReturnerType | Former::ArrowType | Former::LinearArrowType | Former::ProductType | Former::SumType | Former::LazyProductType | Former::TelescopeType | Former::LabelledSumType | Former::LazyRecordType | Former::ParenthesizedType | Former::PathType | Former::BridgeType | Former::FlowType | Former::RelationType | Former::ManifestType | Former::CapabilityType | Former::AtType | Former::StagedType | Former::ModedType | Former::Scope | Former::Declaration | Former::AttributeBlock | Former::Visibility | Former::Import | Former::Module | Former::Data | Former::Mutual | Former::Instantiation | Former::SessionType | Former::Action | Former::Access | Former::World | Former::WorldDeclaration | Former::Reserved(_) | Former::Unadmitted(_) | Former::Misplaced => ret == Ending::Inferred,
})]
fn ending(former: Former) -> Ending
{
    match former {
        Former::Exit | Former::Become | Former::Break | Former::Continue => Ending::Exit,
        Former::Block
        | Former::Case
        | Former::If
        | Former::Offer
        | Former::LazyRecord
        | Former::Parenthesized
        | Former::Lambda
        | Former::Hole
        | Former::Loop
        | Former::While
        | Former::For => Ending::Passes,
        Former::Name
        | Former::Constructor
        | Former::Number
        | Former::Boolean
        | Former::Text
        | Former::Character
        | Former::TypeQuote
        | Former::Thunk
        | Former::Return
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::ForgetModel
        | Former::Telescope
        | Former::List
        | Former::PackModel
        | Former::Injection
        | Former::Binary
        | Former::Unary
        | Former::Projection
        | Former::Instantiation
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
        | Former::Access
        | Former::World
        | Former::WorldDeclaration
        | Former::Reserved(_)
        | Former::Unadmitted(_)
        | Former::Misplaced => Ending::Inferred,
    }
}

/// How `former`, standing where a path through a loop's body ends, treats
/// that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the four exits are the exit; a block, a match, an offer, a
///   grouping and a hole pass the end on; every other former, a nested loop
///   among them, takes the inferred re-entry.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a loop ending in `continue`, in a match whose arms break
///   or end in a call, and in a call each lower and run; one ending in a hole
///   is left to be filled.
/// - witness: `gandr-surface-lowering::lower::loops::tests::a_loop_body_ends_by_its_exits_or_runs_again`
/// - witness: `gandr-surface-lowering::lower::loops::tests::a_hole_ending_a_loop_body_is_left_to_be_filled`
#[spec(ensures: |ret| match former {
    Former::Exit | Former::Become | Former::Break | Former::Continue => ret == Ending::Exit,
    Former::Block | Former::Case | Former::If | Former::Offer | Former::Parenthesized | Former::Hole => ret == Ending::Passes,
    Former::Name | Former::Constructor | Former::Number | Former::Boolean | Former::Text | Former::Character | Former::TypeQuote | Former::Thunk | Former::Lambda | Former::Return | Former::Loop | Former::While | Former::For | Former::Force | Former::Run | Former::Call | Former::ForgetModel | Former::Telescope | Former::List | Former::PackModel | Former::Injection | Former::LazyRecord | Former::Binary | Former::Unary | Former::Projection | Former::TypeHead | Former::TypePath | Former::Universe | Former::TypeApplication | Former::ThunkType | Former::ReturnerType | Former::ArrowType | Former::LinearArrowType | Former::ProductType | Former::SumType | Former::LazyProductType | Former::TelescopeType | Former::LabelledSumType | Former::LazyRecordType | Former::ParenthesizedType | Former::PathType | Former::BridgeType | Former::FlowType | Former::RelationType | Former::ManifestType | Former::CapabilityType | Former::AtType | Former::StagedType | Former::ModedType | Former::Scope | Former::Declaration | Former::AttributeBlock | Former::Visibility | Former::Import | Former::Module | Former::Data | Former::Mutual | Former::Instantiation | Former::SessionType | Former::Action | Former::Access | Former::World | Former::WorldDeclaration | Former::Reserved(_) | Former::Unadmitted(_) | Former::Misplaced => ret == Ending::Inferred,
})]
fn iterating(former: Former) -> Ending
{
    match ending(former) {
        Ending::Exit => Ending::Exit,
        Ending::Passes
            if matches!(
                former,
                Former::Block
                    | Former::Case
                    | Former::If
                    | Former::Offer
                    | Former::Parenthesized
                    | Former::Hole
            ) =>
        {
            Ending::Passes
        },
        Ending::Passes | Ending::Inferred => Ending::Inferred,
    }
}

/// Whether a block-like form ends its statement with no `;` after it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Ends(bool);

/// The argument lists a type operator's use writes after its head (#5213).
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Lists
{
    /// No list, or the one list a static application reads, which calls a
    /// dynamic function only when it holds an argument.
    Bare,
    /// One list written after the head, which calls it even when it is
    /// empty, `f()`.
    Called,
    /// A second list, which applies the call's result once more, `f(a)(b)`.
    Again(Stretch),
}

/// Where a scan of a function form's pieces stands: before its parameter
/// list, inside it, after its closer, or after the arrow of its result.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HeaderAt
{
    /// Before the list's `(`.
    Head,
    /// Between the list's `(` and `)`.
    Listed,
    /// After the list's `)`.
    Closed,
    /// After the `->` that the result type follows.
    Arrow,
}

quenchant_shape::reason_enum! {
    /// Why a written binder hides no binding.
    pub mod hidden {
        /// Nothing the shadow index keeps answers the binder's name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No binder, opened member, declaration, import or builtin
            /// answers the name.
            Unbound,
            /// The innermost binder of the name is one the source writes
            /// nowhere.
            Unwritten,
            /// The lookup past the binders refuses the name: a member declared
            /// later, or a name two scopes answer.
            Refused,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a call's head names no type former.
    pub mod formed {
        /// The head is not a type former's spelling, free.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is no capitalised name, spells no former a type
            /// application takes, or names a binder, an earlier declaration
            /// or a stated type that shadows the former.
            Unformed,
        }
    }
}

/// Where a span stands against the static lambdas' bodies.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Within
{
    /// Inside a static lambda's body, where a call is a static application.
    StaticBody,
    /// Outside every static lambda's body.
    Elsewhere,
}

quenchant_shape::reason_enum! {
    /// Why a `let` statement's binder splits no tuple.
    pub mod untupled {
        /// The binder is a name, a wildcard or another pattern.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The binder is not a tuple pattern.
            OtherPattern,
        }
    }
}

/// The components of a tuple pattern, in written order: each its label when
/// written `.l` or `.l = p`, and its pattern, the label itself for `.l`.
type TupleComponents = Vec<(Option<Placed>, Placed)>;

quenchant_shape::reason_enum! {
    /// Why a `let` statement's at pattern opens no handle.
    pub mod unopened {
        /// The pattern under `at` is no name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A tuple, a wildcard or another pattern stands under `at`.
            OtherPattern,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a documentation link keeps no declaration.
    pub mod linked {
        /// The link resolves, but to no declaration of the unit.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A module, a constructor or a built-in name answers the link.
            Undeclared,
        }
    }
}

/// The unit's declared names by spelling alone, each read once: what a
/// documentation link answers outside the containers around it, in an
/// ordered-map lookup and never a walk of the collection.
#[derive(Debug, Default)]
struct LinkNames<'source>
{
    /// Each declared name, at the first slot of that name in container order.
    slots: BTreeMap<SurfaceName<'source>, SlotIndex>,
    /// Each module name, at the first module of that name in container order.
    modules: BTreeMap<SurfaceName<'source>, StructureIndex>,
    /// Each constructor name.
    constructors: BTreeSet<SurfaceName<'source>>,
}

impl<'source> LinkNames<'source>
{
    /// The names `collected` declares, each at its first holder in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each name a slot, a module or a constructor of `collected`
    ///   takes, the slot and the module at the first entry of that name in the
    ///   collection's key order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a link to a name declared in another module keeps the
    ///   declaration, and a link to a constructor answers.
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_keeps_the_declaration_it_resolves_to_4963`
    #[spec(ensures: |ret| ret.slots.len() <= collected.by_name.len())]
    fn of(collected: &Collected<'source>) -> Self
    {
        let mut names = Self::default();
        for (&(_, name), &slot) in &collected.by_name {
            names.slots.entry(name).or_insert(slot);
        }
        for (&(_, name), &module) in &collected.modules {
            names.modules.entry(name).or_insert(module);
        }
        names.constructors = collected
            .constructors
            .keys()
            .map(|&(_, name, _)| name)
            .collect();
        names
    }
}

quenchant_shape::reason_enum! {
    /// Why a path's head reads no aliased import.
    mod alias_member {
        /// The reason the head is no alias.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head names no alias of a path import of the source.
            Unaliased,
        }
    }
}

/// A recursive tail's own name, from the reading of its body to the frame
/// that binds it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OwnName
{
    /// The name's tile, the tail's staging and the parameter store's mark
    /// before the tail's first parameter, until the name binds.
    pending: Option<(Placed, native::Staging, At)>,
    /// The frame binding the name, once it binds.
    bound: Maybe<ScopeId, recursion::Absent>,
}

/// The continuation type's head, resolved after every binder and earlier
/// declaration at two arguments.
const STACK: &str = "Stack";

/// The infix spellings that call the prelude's declaration of their row's name.
///
/// The model resolves from the operands (`crate::prelude`): `==` is the
/// equality of `Eq`, and `<`, `<=`, `>` and `>=` are the order of `Ord`.
pub const THROUGH_PRELUDE: [&str; 5] = ["==", "<", "<=", ">", ">="];

/// Whether a module's own slot holds a half that lowers to a core term.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two distinct answers, so
///   [`Lowerer::outcome`](crate::lower::ExpressionsRef::outcome) reads an
///   absent outcome of a slot that owes a declaration as a refusal and of any
///   other slot as the absence it is.
/// - provides: the answer of
///   [`Lowerer::lowers_a_half`](crate::lower::ExpressionsRef::lowers_a_half).
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function whose halves the mint left unminted owes a
///   declaration and is refused by name.
/// - witness: `gandr-surface-lowering::lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Owed
{
    /// A half lowers to a core term, so the slot owes a declaration.
    Owed,
    /// No half lowers to a core term.
    Nothing,
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag denotes admission to the syntactic value class, not
///   successful name resolution or type checking.
/// - provides: A value-form decision kept distinct from other Boolean
///   decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tested former is not retained; `is_value_form`
///   specifies the finite membership relation.
///
/// # Adequacy
/// - hypothesis: L3 — the finite former table distinguishes syntactic values
///   from computations and type forms before payload schema checks.
/// - witness: `gandr-surface-lowering::lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueForm(pub bool);

/// Whether a spelling is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag distinguishes a well-formed fractional spelling, which
///   states no type, from a malformed integer spelling.
/// - provides: A lexical refusal decision distinct from numeric evaluation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No input text is retained; fractional states the
///   executable numeric-language predicate.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent markers, missing fields, signs and
///   non-ASCII digits separate unsupported numbers from malformed lexemes.
/// - witness: `gandr-surface-lowering::lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `gandr-surface-lowering::lower::tests::a_number_takes_float64_from_its_suffix_or_annotation_1830`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fractional(pub bool);

/// Whether a node is a type a module signature states, read in the
/// signature's scope: the signature's text, minted though the member it states
/// is refused.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: carries only the flag.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the flag holds no node; `stated_apart` and `mint_at`
///   check it and its effect.
///
/// # Adequacy
/// - hypothesis: L3 — a refused member's stated type answers for itself, and
///   its body stays unminted.
/// - witness: `gandr-surface-lowering::lower::tests::a_signature_s_types_answer_whatever_its_members_1115`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct StatedApart(bool);

/// Whether a binder's written type holds a function: a thunk type or the
/// bridge, read through each type family it names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: carries only the flag.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the flag holds no node; `holds_function` sets it and
///   `static_application` reads it.
///
/// # Adequacy
/// - hypothesis: L3 — a binder at a type member standing for the bridge is
///   called where a type is read.
/// - witness: `gandr-surface-lowering::lower::tests::a_binder_at_a_family_standing_for_a_function_unquotes_its_call_522`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct HoldsFunction(bool);

/// The tables that a document's module resumes with after a closure.
///
/// A closure's own module finishes with these tables, and a document's module
/// resumed after the closure leads with them: the binders in scope, the
/// resolutions and the nested sites, built once when the closure's lowering
/// is suspended, and the tables by declaration and the declarations, shared
/// with every module resumed after the closure.
///
/// # Specification
/// - requires: built by [`Finished::of`] from the module the closure's
///   suspended lowering finishes alone.
/// - ensures: each table, and the declarations, are that module's.
/// - panics: none.
/// - executable: none — a carrier; `Lowerer::finish` states what it builds from
///   it.
///
/// # Adequacy
/// - hypothesis: L3 — a document resumed after its closure lowers to the module
///   the whole lowering does.
/// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[derive(Clone, Debug)]
pub struct Finished<'source>
{
    /// The binders in scope at each span the closure's lowering read under one.
    pub in_scope: crate::InScope,
    /// Each written name the closure's lowering resolved, ascending by span.
    pub resolutions: Vec<(ByteSpan, crate::Resolution)>,
    /// The site of each syntax node of the closure a computation was nested
    /// at.
    pub nested: BTreeMap<NodeIndex, NestedSite>,
    /// The tables a declaration's checking reads by its key, at the closure's
    /// declarations.
    pub keyed: KeyedTables<'source>,
    /// The closure's declarations, in admission order.
    pub declarations: Arc<[LoweredDeclaration<'source>]>,
}

impl<'source> Finished<'source>
{
    /// The tables `module`, a closure's own, finished with, beside its origin
    /// table, which records the closure's declarations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(mut module: LoweredModule<'source>) -> (Self, OriginTable)
    {
        let keyed = module.take_keyed_tables();
        let declarations = module.take_declarations();
        let origins = core::mem::replace(module.origins_mut(), OriginTable::new());
        let (in_scope, resolutions, nested) = module.into_scope_tables();
        (
            Self {
                in_scope,
                resolutions,
                nested,
                keyed,
                declarations,
            },
            origins,
        )
    }
}

/// Where a lowering resumed after a closure's began: the closure's finished
/// tables, and the length each list the finish reads had at the closure's
/// end.
///
/// # Specification
/// - requires: built by
///   [`Lowerer::resumed`](crate::lower::ExpressionsRef::resumed) from the
///   closure's suspended lowering before any later source is read into it.
/// - ensures: every entry a list holds past its mark was made by a source after
///   the closure's.
/// - panics: none.
/// - executable: none — the marks are positions into lists this record does not
///   hold.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Finished`].
/// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[derive(Clone, Copy, Debug)]
pub struct Resumed<'finished, 'source>
{
    /// The closure's finished tables.
    pub finished: &'finished Finished<'source>,
    /// The closure's declarations: the slots collected before the document's.
    pub slots: usize,
    /// The closure's blocks: the blocks read before the document's.
    pub blocks: LayoutBlock,
    /// The origin values recorded before the document's.
    pub values: usize,
    /// The resolutions recorded before the document's.
    pub resolved: usize,
    /// The declared uses collected before the document's.
    pub declared: usize,
}

/// Whether a node or a slot belongs to the source being lowered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Ours(bool);

/// Where `half` is written: its form's bytes and its name tile's.
///
/// # Specification
/// trivial.
const fn half_at(half: Half) -> HalfAt
{
    HalfAt {
        span: half.declaration.span,
        named: half.named.span,
    }
}

/// The documentation a lowering files: each documented form's, and each
/// source's own.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Filed<'source>
{
    /// Each documented form's documentation, by its unit key.
    pub forms: BTreeMap<UnitKey, Documentation<'source>>,
    /// Each source's own documentation, its `//!` runs, by the source.
    pub sources: BTreeMap<SourceIndex, Documentation<'source>>,
}

/// The expression and type lowering over its host.
///
/// The host holds the lowering's context and answers each call into a family.
/// A call from the lowering into the expression lowering builds
/// `Expressions::new(self)`.
#[repr(transparent)]
pub struct Expressions<'host, F>
{
    /// The host: the lowering, which holds the context and the families.
    host: &'host mut F,
}

impl<'host, F> Expressions<'host, F>
{
    /// The expression lowering over `host`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(host: &'host mut F) -> Self
    {
        Self { host }
    }
}

/// The expression lowering's reads over its host.
///
/// Each read reads the lowering's context and answers a minting through the
/// host, so a read borrows the host and never writes it. A call from a
/// reading of the lowering builds `ExpressionsRef::new(self)`.
#[repr(transparent)]
pub struct ExpressionsRef<'host, F>
{
    /// The host: the lowering, which holds the context and the families.
    host: &'host F,
}

impl<'host, F> ExpressionsRef<'host, F>
{
    /// The expression lowering's reads over `host`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(host: &'host F) -> Self
    {
        Self { host }
    }
}

/// The reads' way to their state and to the families.
impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The lowering's context, to read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cx(&self) -> &Context<'run, 'source>
    {
        self.host.context()
    }

    /// The family that answers a minting into another family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn host_ref(&self) -> &F
    {
        self.host
    }
}

/// The expression lowering's way to its state and to the families: each read
/// is the host's context, and each call into a family is the host's.
impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The lowering's context, to read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cx(&self) -> &Context<'run, 'source>
    {
        self.host.context()
    }

    /// The lowering's context, to write.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cx_mut(&mut self) -> &mut Context<'run, 'source>
    {
        self.host.context_mut()
    }

    /// The family that answers a call into a family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn host(&mut self) -> &mut F
    {
        self.host
    }

    /// The family that answers a minting into a family, to read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn host_ref(&self) -> &F
    {
        self.host
    }

    /// The expression lowering's reads, which borrow the host and never write
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn shared(&self) -> ExpressionsRef<'_, F>
    {
        ExpressionsRef::new(self.host)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Lower `source`, whose top-level forms are `pieces`: its collection and
    /// every pass over it, minting into `sink`.
    ///
    /// # Specification
    /// - requires: every source before `source` is lowered, and none after.
    /// - ensures: `source`'s declarations are collected and every pass over
    ///   them has run, its core nodes minted into `sink` after the earlier
    ///   sources', and its nodes' entries forgotten ([`Self::end_source`]).
    /// - provides: one step of `lower_unit`, and what a resumed lowering takes
    ///   after its closure's.
    /// - fails: the module-level refusals `lower_unit` names, raised by this
    ///   source.
    /// - panics: none.
    ///
    /// # Errors
    /// As the specification's fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as `lower_unit`.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: |result| result.is_err() || self.cx().current.source == source)]
    #[inline]
    pub fn lower_source(
        &mut self,
        source: SourceIndex,
        pieces: Vec<Piece>,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.begin_source(source, pieces)?;
        self.define_members(source);
        self.refuse_imports();
        self.declare();
        self.mark_generic();
        self.seed()?;
        Exits::new(self.host()).survey()?;
        self.classify()?;
        Identities::new(self.host()).refuse_unsynthesised()?;
        self.propagate_manifests();
        while self.refuse_unrepresented().0 {
            self.propagate_manifests();
        }
        Native::new(self.host()).refuse_sibling_arities();
        Native::new(self.host()).unjoin_refused();
        CapabilityRef::new(self.host_ref()).mint_foreign(sink);
        self.mint(sink)?;
        Native::new(self.host()).mint_joints(sink);
        self.mint_abstracts(sink);
        Models::new(self.host()).mint_models(sink);
        Models::new(self.host()).match_signatures(sink);
        self.check_requirements();
        self.mint_requirements(sink);
        Models::new(self.host()).check_families(sink);
        Models::new(self.host()).check_sorts();
        Native::new(self.host()).mint_data(sink);
        self.mint_descriptions(sink)?;
        self.mint_presentations(sink)?;
        self.mint_operations(sink);
        Models::new(self.host()).mint_derived_rules(sink);
        Models::new(self.host()).refuse_derived_components();
        self.mint_boundaries(sink);
        self.mint_generics(sink);
        Models::new(self.host()).mint_reducts(sink);
        Models::new(self.host()).mint_forgets(sink);
        self.mint_instances(sink);
        self.mint_paths(sink);
        self.refuse_misshapen_entries(sink);
        self.place_by_layout();
        self.place_misspelt();
        self.place_misspelt_operator();
        self.place_bare_index();
        self.refused_declarations();

        self.end_source();
        Ok(())
    }

    /// Forget what the lowering kept about the nodes of the source it has
    /// just lowered: every table keyed by a syntax node that the passes read
    /// only while that node's source is lowered.
    ///
    /// A later source's passes look up only their own nodes, and a lowering
    /// suspended after its closure holds none of the closure's entries, so a
    /// document resumed after it neither copies nor searches them.
    ///
    /// # Specification
    /// - requires: every pass over the current source has run.
    /// - ensures: each of those tables is empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source lowers alike whatever precedes and follows
    ///   it, and a document resumed after its closure lowers as the whole unit
    ///   does.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: self.cx().classifiers.is_empty()
        && self.cx().argued.is_empty()
        && self.cx().awaiting.is_empty()
        && self.cx().fielded.is_empty()
        && self.cx().thunked.is_empty()
        && self.cx().inherited.is_empty()
        && self.cx().stand_ins.is_empty()
        && self.cx().defining.is_empty()
        && self.cx().kinds.is_empty()
        && self.cx().fixed_sorts.is_empty()
        && self.cx().answers.is_empty()
        && self.cx().cocased.is_empty()
        && self.cx().in_type.is_empty()
        && self.cx().in_quote.is_empty()
        && self.cx().at_endpoint.is_empty()
        && self.cx().exits.is_empty()
        && self.cx().exitable.is_empty()
        && self.cx().joined.is_empty()
        && self.cx().leaving.is_empty()
        && self.cx().iterated.is_empty()
        && self.cx().looping.is_empty()
        && self.cx().breaking.is_empty()
        && self.cx().reentered.is_empty()
        && self.cx().tested.is_empty()
        && self.cx().threading.is_empty()
        && self.cx().carries.is_empty()
        && self.cx().results.is_empty()
        && self.cx().framed.is_empty()
        && self.cx().looped_past.is_empty()
        && self.cx().bodies.is_empty()
        && self.cx().crossing.is_empty()
        && self.cx().delimited.is_empty()
        && self.cx().inferred.is_empty()
        && self.cx().stated.is_empty()
        && self.cx().stated_tails.is_empty()
        && self.cx().trailing.is_empty()
        && self.cx().stage_marks.is_empty()
        && self.cx().pattern_stated.is_empty()
        && self.cx().scrutinised.is_empty()
        && self.cx().descents.is_empty()
        && self.cx().injected.is_empty()
        && self.cx().sibling_calls.is_empty()
        && self.cx().type_read.is_empty()
        && self.cx().valued_telescopes.is_empty()
        && self.cx().nullary.is_empty()
        && self.cx().typed_heads.is_empty()
        && self.cx().supplied.is_empty()
        && self.cx().regions.is_empty()
        && self.cx().static_lambdas.is_empty()
        && self.cx().static_spans.is_empty()
        && self.cx().static_calls.is_empty()
        && self.cx().unresolved.is_empty())]
    fn end_source(&mut self)
    {
        self.cx_mut().classifiers.clear();
        self.cx_mut().argued.clear();
        self.cx_mut().awaiting.clear();
        self.cx_mut().fielded.clear();
        self.cx_mut().thunked.clear();
        self.cx_mut().inherited.clear();
        self.cx_mut().stand_ins.clear();
        self.cx_mut().defining.clear();
        self.cx_mut().kinds.clear();
        self.cx_mut().fixed_sorts.clear();
        self.cx_mut().answers.clear();
        self.cx_mut().cocased.clear();
        self.cx_mut().in_type.clear();
        self.cx_mut().in_quote.clear();
        self.cx_mut().at_endpoint.clear();
        self.cx_mut().exits.clear();
        self.cx_mut().exitable.clear();
        self.cx_mut().joined.clear();
        self.cx_mut().leaving.clear();
        self.cx_mut().iterated.clear();
        self.cx_mut().looping.clear();
        self.cx_mut().breaking.clear();
        self.cx_mut().reentered.clear();
        self.cx_mut().tested.clear();
        self.cx_mut().threading.clear();
        self.cx_mut().carries.clear();
        self.cx_mut().results.clear();
        self.cx_mut().framed.clear();
        self.cx_mut().looped_past.clear();
        self.cx_mut().bodies.clear();
        self.cx_mut().crossing.clear();
        self.cx_mut().delimited.clear();
        self.cx_mut().inferred.clear();
        self.cx_mut().stated.clear();
        self.cx_mut().stated_tails.clear();
        self.cx_mut().trailing.clear();
        self.cx_mut().stage_marks.clear();
        self.cx_mut().pattern_stated.clear();
        self.cx_mut().scrutinised.clear();
        self.cx_mut().descents.clear();
        self.cx_mut().injected.clear();
        self.cx_mut().sibling_calls.clear();
        self.cx_mut().type_read.clear();
        self.cx_mut().valued_telescopes.clear();
        self.cx_mut().nullary.clear();
        self.cx_mut().typed_heads.clear();
        self.cx_mut().supplied.clear();
        self.cx_mut().regions.clear();
        self.cx_mut().static_lambdas.clear();
        self.cx_mut().static_spans.clear();
        self.cx_mut().static_calls.clear();
        self.cx_mut().unresolved.clear();
    }

    /// Keep each top-level type member of `source` that takes no parameters,
    /// by the node of its definition, with the name tile it declares. A
    /// definition that is itself a type name, `type Temp = Fahrenheit`, keeps
    /// that name's spelling, so the map leaves it out.
    ///
    /// # Specification
    /// - requires: `source`'s declarations are collected.
    /// - ensures: [`Context::defining`](gandr_surface_lowering_base::lower::Context::defining) holds exactly the definition of each
    ///   member [`Collected::top_types`] files under `source` with a manifest
    ///   meaning, other than a bare type head or a type path, beside the name
    ///   tile of its slot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member's own name names the record its definition
    ///   mints, beside three bases written by that name; a record written in
    ///   place keeps no name.
    /// - witness: `gandr-surface-lowering::lower::patched::tests::a_base_named_by_a_type_member_keeps_the_name`
    #[spec(ensures: self.cx().defining.len() <= self.cx().collected.top_types.len())]
    fn define_members(
        &mut self,
        source: SourceIndex,
    )
    {
        self.cx_mut().defining = self
            .cx()
            .collected
            .top_types
            .iter()
            .filter(|&&(filed, _)| filed == source)
            .filter_map(|&(_, member)| match member.meaning {
                TypeMeaning::Manifest(defined)
                    if !matches!(
                        self.cx().form_at(defined),
                        Ok(Some((_, Former::TypeHead | Former::TypePath)))
                    ) =>
                {
                    self.cx()
                        .collected
                        .slots
                        .get(usize::from(member.held))
                        .map(|slot| (defined.node, slot.named.node))
                },
                TypeMeaning::Manifest(_) => None,
                TypeMeaning::Sealed | TypeMeaning::Instantiated { .. } | TypeMeaning::Family(_) => {
                    None
                },
            })
            .collect();
    }

    /// Rebind the lowering to `tree`, which lays more nodes after the ones
    /// it read, under `unit`, which lays more sources after the ones it
    /// lowered, `described` the description reading of the roots `tree`
    /// adds, its rule blocks decided through `decisions`.
    ///
    /// # Specification
    /// - requires: `tree`'s first nodes are the nodes the lowering read, at the
    ///   same positions over the same text, and `unit`'s first sources the ones
    ///   it lowered; `described` is [`crate::description::elaborate_roots`]
    ///   over the added roots, numbered after the descriptions collected.
    /// - ensures: one cell per node of `tree` in every per-node table, the
    ///   added nodes' as `Lowerer::new` makes them and the read nodes' kept;
    ///   the collection widened as [`Collected::widen`] says; every node's
    ///   source read over `tree`; the holes, once read, read over `tree`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document resumed after its closure lowers as the
    ///   whole unit does, holes and descriptions included.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: self.cx().readings.count() == tree.node_count()
        && self.cx().source_of.count() == tree.node_count())]
    #[inline]
    pub fn widen(
        &mut self,
        tree: &'run SyntaxTree<'source>,
        unit: &Unit,
        described: crate::description::DescriptionReport,
        decisions: &mut Decisions,
    )
    {
        let read = self.cx().readings.blocks();
        self.cx_mut().tree = tree;
        self.cx_mut().readings.widen(tree.blocks(), Reading::Unread);
        self.cx_mut().plans.widen(tree.blocks(), Plan::Unplanned);
        self.cx_mut().taken.widen(tree.blocks(), false);
        self.cx_mut().bridges.widen(tree.blocks(), Bridge::Bare);
        self.cx_mut()
            .lowered
            .widen(tree.blocks(), Maybe::Absent(lowered::Absent::Unminted));
        self.cx_mut().payload.widen(tree.blocks(), InPayload(false));
        self.cx_mut()
            .scopes
            .widen(tree.blocks(), Maybe::Absent(scoped::Absent::Unscoped));
        self.cx_mut()
            .leaves
            .widen(tree.blocks(), exits::Leaves::Never);
        self.cx_mut()
            .collected
            .widen(tree, unit, described, decisions);
        extend_sources(&mut self.cx_mut().source_of, tree, unit);
        if !self.cx().holes.is_empty() {
            self.read_holes(read);
        }
    }

    /// Share every per-node table's cells, and the collection's descriptions
    /// and model signatures, so a lowering resumed from a clone of this one
    /// copies none of them and widens by its own alone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every per-node table holds the cells it held, and each
    ///   layered table of the collection the entries it held, all of them
    ///   shared.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — each table's `Lowerer::share` or
    ///   [`gandr_surface_lowering_base::layered::Layered::share`] states its
    ///   own clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document resumed after its closure lowers as the
    ///   whole does.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[inline]
    pub fn share_tables(&mut self)
    {
        self.cx_mut().readings.share();
        self.cx_mut().plans.share();
        self.cx_mut().taken.share();
        self.cx_mut().bridges.share();
        self.cx_mut().lowered.share();
        self.cx_mut().payload.share();
        self.cx_mut().scopes.share();
        self.cx_mut().leaves.share();
        self.cx_mut().source_of.share();
        self.cx_mut().collected.owner.share();
        self.cx_mut().collected.descriptions.share();
        self.cx_mut().collected.models.share();
    }

    /// Begin lowering `source`: mark where its share of each list begins and
    /// collect its top-level forms `pieces`.
    ///
    /// # Specification
    /// - requires: every source before `source` is lowered, and `pieces` are
    ///   `source`'s root pieces.
    /// - ensures: the current source is `source`, with its own positions and
    ///   each mark at the length its list had before the collection; the
    ///   source's forms are collected after the earlier sources'.
    /// - provides: the start of each source's lowering.
    /// - fails: as [`collect_source`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`collect_source`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source lowers to the same declarations and the same
    ///   leading arena rows whether or not another source follows it.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
    #[spec(ensures: |_| self.cx().current.source == source && self.cx().current.slots <= self.cx().collected.slots.len())]
    fn begin_source(
        &mut self,
        source: SourceIndex,
        pieces: Vec<Piece>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.cx_mut().own = own_positions(&self.cx().source_of, source);
        self.cx_mut().current = Current {
            source,
            slots: self.cx().collected.slots.len(),
            structures: self.cx().collected.structures.len(),
            data: self.cx().collected.data.len(),
            words: self.cx().collected.words.len(),
            terms: self.cx().collected.terms.len(),
            families: self.cx().collected.families.len(),
            functors: self.cx().collected.functors.len(),
            instances: self.cx().collected.instances.len(),
            blocks: self.cx().collected.blocks.len(),
            decorated: self.cx().collected.decorated.len(),
            scopes: self.cx().collected.scopes.len(),
            synthesised: self.cx().synthesised.len(),
            labels: self.cx().labels.len(),
            data_frames: self.cx().data_frames.len(),
            lettered: self.cx().lettered.len(),
            pointed: self.cx().pointed.len(),
        };
        let cx = self.cx_mut();
        collect_source((cx.pbg, cx.tree), &mut cx.collected, &mut cx.fuel, pieces)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Whether `slot` was admitted while lowering the current source.
    ///
    /// # Specification
    /// trivial.
    fn owns_slot(
        &self,
        slot: SlotIndex,
    ) -> Ours
    {
        Ours(usize::from(slot) >= self.cx().current.slots)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Refuse what a source's imports forbid: every declaration of a source
    /// with an import that resolved to no source, that is an edge of a cycle,
    /// or whose list names what its module does not export, and every
    /// top-level declaration or constructor of a source that an unqualified
    /// import binds again.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each slot whose name stands in a source with a path import
    ///   resolved to [`ImportTarget::Unresolved`] or [`ImportTarget::Cycle`]
    ///   holds [`LoweringRefusal::ImportUnresolved`] or
    ///   [`LoweringRefusal::ImportCycle`] at its declaration form, naming the
    ///   import; each slot of a source whose import is read via a name no flow
    ///   bears holds [`LoweringRefusal::NotATranslation`] at the name, and one
    ///   whose import's source publishes nothing of a name the flow's domain
    ///   states holds [`LoweringRefusal::SignatureMismatch`] at the flow's
    ///   name, naming the first such member — except a slot of a functor's
    ///   template, which declares nothing; each slot of a source whose import
    ///   lists a name its module neither declares nor homes holds
    ///   [`LoweringRefusal::UnknownMember`], and one its module keeps private
    ///   [`LoweringRefusal::UnexportedName`], at the listed name; each
    ///   top-level declared name, and each family whose constructor, a source
    ///   imports from another that exports it under that name, every export or
    ///   a listed one, holds [`LoweringRefusal::ImportShadows`] at its name,
    ///   naming the import and the imported declaration — except a constructor
    ///   the import entered as the very same constructor, as every source whose
    ///   block takes the one `Theory` enters its constructors. A declaration
    ///   its source keeps private binds nothing in an importer. An import
    ///   resolved to [`ImportTarget::Unlocked`] refuses nothing here: it binds
    ///   nothing, and a name read through it is refused where it is read. The
    ///   import itself, and every source without such an import, is untouched.
    /// - provides: the per-declaration refusal the corpus pins an import's
    ///   failure by.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unresolved import, a cycle and a shadowing
    ///   declaration each refuse the importer's declarations by name, in the
    ///   corpus's pathological twins.
    /// - witness: `gandr-surface-lowering::tests::namespace::an_unresolved_import_refuses_its_source`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_declaration_an_import_binds_again_is_refused`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_private_declaration_is_refused_to_its_importer_2687`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_import_list_binds_only_the_names_it_lists_2687`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_via_reads_a_flow_declared_before_it_or_published_by_its_source_3378`
    #[spec(
        captures: before = self.cx().collected.slots.len(),
        ensures: self.cx().collected.slots.len() == before,
    )]
    fn refuse_imports(&mut self)
    {
        let collected = &self.cx().collected;
        let named_at = |slot: SlotIndex| {
            collected
                .slots
                .get(usize::from(slot))
                .map(|found| found.named.span)
        };
        let mut refusals: Vec<(SlotIndex, LoweringRefusal<'source>)> = Vec::new();
        for import in collected.imports.declarations() {
            let source = import.source();
            if source != self.cx().current.source {
                continue;
            }
            let (ImportResolution::Path(target), span) = (import.resolution(), import.span())
            else {
                continue;
            };
            let imported = match target {
                ImportTarget::Source(imported) => imported,
                ImportTarget::Unlocked => continue,
                ImportTarget::Unresolved | ImportTarget::Cycle => {
                    for (index, slot) in collected.slots.iter().enumerate() {
                        if collected.unit.source_at(slot.named.span.start()) != source {
                            continue;
                        }
                        let refused = slot.named.span;
                        refusals.push((SlotIndex::from(index), match target {
                            ImportTarget::Cycle => LoweringRefusal::ImportCycle { span, refused },
                            ImportTarget::Unresolved
                            | ImportTarget::Source(_)
                            | ImportTarget::Unlocked => {
                                LoweringRefusal::ImportUnresolved { span, refused }
                            },
                        }));
                    }
                    continue;
                },
            };
            if let &Maybe::Present(ImportSignature {
                via:
                    Maybe::Present(Translation {
                        named,
                        name,
                        flow: Maybe::Absent(_),
                        ..
                    }),
                ..
            }) = import.signature()
            {
                for (index, slot) in collected.slots.iter().enumerate() {
                    if collected.unit.source_at(slot.named.span.start()) == source
                        && collected.stratum_of(slot.container) == Stratum::Module
                    {
                        refusals.push((SlotIndex::from(index), LoweringRefusal::NotATranslation {
                            span: named.span,
                            name,
                            refused: slot.named.span,
                        }));
                    }
                }
                continue;
            }
            if let &Maybe::Present(ImportSignature {
                via:
                    Maybe::Present(Translation {
                        named,
                        flow: Maybe::Present(flow),
                        lacking: Maybe::Present(member),
                        ..
                    }),
                ..
            }) = import.signature()
                && let Some(&Functor {
                    scope: BodyScope::Domain { ref domain, .. },
                    ..
                }) = collected.functors.get(usize::from(flow))
            {
                let theory = self.cx().name_at(domain.named);
                for (index, slot) in collected.slots.iter().enumerate() {
                    if collected.unit.source_at(slot.named.span.start()) == source
                        && collected.stratum_of(slot.container) == Stratum::Module
                    {
                        refusals.push((
                            SlotIndex::from(index),
                            LoweringRefusal::SignatureMismatch {
                                span: named.span,
                                signature: theory,
                                member,
                                fault: MatchFault::Missing,
                                refused: slot.named.span,
                            },
                        ));
                    }
                }
                continue;
            }
            if *import.opening() == Opening::Nothing {
                continue;
            }
            let bound_in_import = |name: SurfaceName<'source>| {
                collected
                    .by_name
                    .get(&(Container::TopLevel(imported), name))
                    .copied()
                    .filter(|&slot| collected.slot_visibility(slot) == Visibility::Public)
                    .and_then(named_at)
                    .or_else(|| {
                        collected
                            .constructors_in(imported, name)
                            .find(|constructor| {
                                collected.slot_visibility(constructor.family) == Visibility::Public
                            })
                            .map(|constructor| constructor.named.span)
                    })
                    .filter(|_| import.opens(name).0)
            };
            if let (&Opening::Listed(ref listed), Maybe::Present(module)) =
                (import.opening(), import.module())
            {
                for &(name, at) in listed {
                    let found = collected.listed_in(imported, name);
                    if let Some((Visibility::Public, _)) = found {
                        continue;
                    }
                    // A head the module homes is listed though no source
                    // declares it: `import std.list (List);` (#4520),
                    // `import std.buffer (Buf);` (#4522).
                    if found.is_none()
                        && (matches!(homed_former(module, name), Maybe::Present(_))
                            || matches!(homed_atom(module, name), Maybe::Present(_)))
                    {
                        continue;
                    }
                    for (index, slot) in collected.slots.iter().enumerate() {
                        if collected.unit.source_at(slot.named.span.start()) != source {
                            continue;
                        }
                        refusals.push((SlotIndex::from(index), match found {
                            Some((Visibility::Public | Visibility::Private, declared)) => {
                                LoweringRefusal::UnexportedName {
                                    span: at,
                                    name,
                                    declared,
                                    reason: Unexported::Private,
                                }
                            },
                            None => LoweringRefusal::UnknownMember {
                                span: at,
                                module,
                                member: name,
                            },
                        }));
                    }
                }
            }
            for (index, slot) in collected.slots.iter().enumerate() {
                if slot.container != Container::TopLevel(source) || slot.role != Role::Declared {
                    continue;
                }
                if let Some(other) = bound_in_import(slot.name) {
                    refusals.push((SlotIndex::from(index), LoweringRefusal::ImportShadows {
                        span: slot.named.span,
                        name: slot.name,
                        import: span,
                        other,
                    }));
                }
            }
            for (&(owner, name, family), constructor) in &collected.constructors {
                if owner != source {
                    continue;
                }
                let entered =
                    collected.constructors.get(&(imported, name, family)) == Some(constructor);
                if !entered && let Some(other) = bound_in_import(name) {
                    refusals.push((constructor.family, LoweringRefusal::ImportShadows {
                        span: constructor.named.span,
                        name,
                        import: span,
                        other,
                    }));
                }
            }
        }
        for (index, refusal) in refusals {
            if let Some(slot) = self.cx_mut().collected.slots.get_mut(usize::from(index)) {
                slot.refuse(slot.introduced_by.node, refusal);
            }
        }
    }

    /// Declare every top-level name over the outermost scope: each top-level
    /// declaration, then each top-level module with the namespace it exports.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each top-level declaration is declared as a definition — a
    ///   `theory` block's governing the path `T.r` of each rule a derived rule
    ///   declaration of its source derives in it, and the path `T.S` of the
    ///   reduct to each theory `S` it includes, as a component, and a theory an
    ///   earlier source declares gaining `T.r` from the deriving source on —
    ///   and each top-level module as a namespace governing exactly the
    ///   components it exports — a value component as a component, a type
    ///   component as a type, a nested module as a namespace of its own, walked
    ///   by an explicit worklist — each tagged with its name tile's bytes and
    ///   displacing the builtin subtree it lands on; every exported value
    ///   component's full path is recorded with the slot a reference reads —
    ///   the member, or the witness an opaque ascription exports in its place —
    ///   and every exported type component's with what it reads. An exported
    ///   slot keeps the role it was declared with, or [`Role::Generic`] once
    ///   the prelude's `Eq.generic` is marked. A declaration the shadow policy
    ///   refuses holds [`LoweringRefusal::ShadowedBuiltin`] at its name,
    ///   offered at its declaration form, and a module so refused files a held
    ///   slot carrying it; the scope keeps the builtin. Module members and
    ///   hidden members are declared nowhere in the outermost scope.
    /// - provides: the outermost half of the module's names, and the governance
    ///   of every module path.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a builtin under each policy and
    ///   over nothing, asserted as the exact record, outcome and resolution; a
    ///   module exporting a component, hiding a member and exporting a nested
    ///   module, each path asserted as the exact resolution. Every exported
    ///   member is checked here once, after the last module, rather than by
    ///   each module's declaration. A module's member, whatever its name,
    ///   shadows no builtin.
    /// - witness: `gandr-surface-lowering::tests::recognition::a_shadowed_builtin_is_reported_as_a_warning`
    /// - witness: `gandr-surface-lowering::tests::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `gandr-surface-lowering::tests::recognition::user_shadowing_is_the_only_observable_delta`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `gandr-surface-lowering::tests::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every slot and every module's exports; the check reads each appended slot and each exported member once"
        )
    )]
    #[spec(
        captures: before = (self.cx().collected.slots.len(), self.cx().collected.structures.len()),
        ensures: |_| {
            self.cx().collected.structures.len() == before.1
                && self.cx().collected.slots.len() >= before.0
                && self.cx().collected.slots.iter().enumerate().skip(before.0).all(
                    |(index, slot)| {
                        slot.role == Role::Held
                            && matches!(slot.container, Container::TopLevel(_))
                            && usize::from(slot.constant) == index
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    },
                )
                && self.cx().exported.values().all(|slot| {
                    self.cx().collected
                        .slots
                        .get(usize::from(*slot))
                        .is_some_and(|entry| matches!(entry.role, Role::Declared | Role::Witness | Role::Derived | Role::Generic | Role::Admitted | Role::Discharged))
                })
        },
    )]
    #[inline]
    pub fn declare(&mut self)
    {
        let (first_slot, first_structure) = (self.cx().current.slots, self.cx().current.structures);
        let mut derived: BTreeMap<SlotIndex, Vec<(SurfaceName<'source>, SlotIndex, ByteSpan)>> =
            BTreeMap::new();
        for (&slot, rule) in self
            .cx()
            .collected
            .derived
            .range(SlotIndex::from(first_slot) ..)
        {
            let Some(entry) = self.cx().collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if self.cx().collected.owner_of(entry.introduced_by.node) == Maybe::Present(slot) {
                derived.entry(rule.presented).or_default().push((
                    entry.name,
                    slot,
                    entry.named.span,
                ));
            }
        }
        // A theory's reduct to a theory it includes joins its namespace as a
        // derived rule does: `T.S` reads the reduct to `S`.
        for (&slot, reduct) in self
            .cx()
            .collected
            .reducts
            .range(SlotIndex::from(first_slot) ..)
        {
            if let Some(entry) = self.cx().collected.slots.get(usize::from(slot)) {
                derived.entry(reduct.source).or_default().push((
                    entry.name,
                    slot,
                    entry.named.span,
                ));
            }
        }
        let cx = self.cx_mut();
        for (position, slot) in cx.collected.slots.iter_mut().enumerate().skip(first_slot) {
            if !matches!(slot.container, Container::TopLevel(_)) || slot.role != Role::Declared {
                continue;
            }
            let site = slot.named.span;
            let mut subtree = Trie::empty();
            let _fresh = subtree.insert(
                &NamePath::root(),
                Binding::new(Recognized::Definition, RecognitionSite::Source(site)),
            );
            for &(rule, statement, at) in derived
                .get(&SlotIndex::from(position))
                .map_or(&[][..], Vec::as_slice)
            {
                let _fresh = subtree.insert(
                    &NamePath::from(Vec::from([Segment::from(rule.as_ref())])),
                    Binding::new(Recognized::ModuleComponent, RecognitionSite::Source(at)),
                );
                let _replaced = cx.exported.insert(
                    NamePath::from(Vec::from([
                        Segment::from(slot.name.as_ref()),
                        Segment::from(rule.as_ref()),
                    ])),
                    statement,
                );
            }
            let declared = cx
                .recognition
                .declare(Segment::from(slot.name.as_ref()), subtree, site);
            if let Err(_refused) = declared {
                slot.refuse(slot.introduced_by.node, LoweringRefusal::ShadowedBuiltin {
                    span: site,
                    name: slot.name,
                });
            }
        }
        // A rule derived in a theory an earlier source declares joins that
        // theory's namespace from here on: `T.r` reads the statement.
        for (&presented, rules) in derived.range(.. SlotIndex::from(first_slot)) {
            let Some(theory) = cx.collected.slots.get(usize::from(presented))
            else {
                continue;
            };
            for &(rule, statement, at) in rules {
                let path = NamePath::from(Vec::from([
                    Segment::from(theory.name.as_ref()),
                    Segment::from(rule.as_ref()),
                ]));
                cx.recognition.declare_component(&path, at);
                let _replaced = cx.exported.insert(path, statement);
            }
        }
        let mut tops: Vec<StructureIndex> = Vec::new();
        let mut shadowing: Vec<StructureIndex> = Vec::new();
        for (position, structure) in cx
            .collected
            .structures
            .iter()
            .enumerate()
            .skip(first_structure)
        {
            if !matches!(structure.container, Container::TopLevel(_)) {
                continue;
            }
            match structure.stratum {
                Stratum::Module | Stratum::Instance(_) => {
                    tops.push(StructureIndex::from(position));
                },
                Stratum::Functor(_) => {
                    let mut subtree = Trie::empty();
                    let _fresh = subtree.insert(
                        &NamePath::root(),
                        Binding::new(
                            Recognized::Functor,
                            RecognitionSite::Source(structure.named.span),
                        ),
                    );
                    if let Err(_refused) = cx.recognition.declare(
                        Segment::from(structure.name.as_ref()),
                        subtree,
                        structure.named.span,
                    ) {
                        shadowing.push(StructureIndex::from(position));
                    }
                },
                Stratum::Parameter(_) => {},
            }
        }
        for functor in shadowing {
            self.refuse_shadowing(functor);
        }
        for top in tops {
            self.declare_module(top);
        }
    }

    /// Declare the top-level module at `top` with the namespace it exports.
    ///
    /// # Specification
    /// - requires: `top` names a closed top-level module.
    /// - ensures: as [`Self::declare`] for one module.
    /// - provides: the per-module half of [`Self::declare`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — only exported value and type paths enter the module
    ///   namespace, while a hidden member stays absent and nested namespaces
    ///   govern their own paths. The predicate reads only the slot this call
    ///   may append; [`Self::declare`] checks every exported member once, after
    ///   the last module.
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `gandr-surface-lowering::tests::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `gandr-surface-lowering::tests::modules::a_signed_member_of_a_sealed_module_exports_its_witness`
    #[spec(
        captures: before = (self.cx().exported.len(), self.cx().exported_types.len(), self.cx().collected.slots.len()),
        ensures: |_| {
            self.cx().exported.len() >= before.0
                && self.cx().exported_types.len() >= before.1
                && self.cx().collected.slots.len() >= before.2
                && self.cx().collected.slots.len() <= before.2.saturating_add(1)
                && self.cx().collected.slots.get(before.2 ..).is_some_and(|appended| {
                    appended.iter().all(|slot| {
                        slot.role == Role::Held
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    })
                })
        },
    )]
    fn declare_module(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.cx().collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named) = (module.name, module.named);
        let root = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        let mut subtree = Trie::empty();
        let _root = subtree.insert(
            &NamePath::root(),
            Binding::new(
                Recognized::ModuleNamespace,
                RecognitionSite::Source(named.span),
            ),
        );
        let mut work = Vec::from([(top, NamePath::root())]);
        while let Some((structure, relative)) = work.pop() {
            let cx = self.cx_mut();
            let Some(entry) = cx.collected.structures.get(usize::from(structure))
            else {
                continue;
            };
            for stated in entry.exported_types() {
                let Some(site) = cx
                    .collected
                    .slots
                    .get(usize::from(stated.held))
                    .map(|held| held.named.span)
                else {
                    continue;
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    stated.name.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(Recognized::ModuleType, RecognitionSite::Source(site)),
                );
                let _replaced = cx.exported_types.insert(root.extended(&path), *stated);
            }
            for &export in &entry.exports {
                let (segment, site, recognized) = match export {
                    Member::Slot(slot) => {
                        let Some(member) = cx.collected.slots.get(usize::from(slot))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleComponent)
                    },
                    Member::Module(nested) => {
                        let Some(member) = cx.collected.structures.get(usize::from(nested))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleNamespace)
                    },
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    segment.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(recognized, RecognitionSite::Source(site)),
                );
                match export {
                    Member::Slot(slot) => {
                        let read = cx.collected.exported_read(structure, slot);
                        let _replaced = cx.exported.insert(root.extended(&path), read);
                    },
                    Member::Module(nested) => work.push((nested, path)),
                }
            }
        }
        let declared =
            self.cx_mut()
                .recognition
                .declare(Segment::from(name.as_ref()), subtree, named.span);
        if let Err(_refused) = declared {
            self.refuse_shadowing(top);
        }
    }

    /// Refuse the top-level module or functor at `top`, whose name shadows a
    /// builtin the active policy protects, on a held slot of its own.
    ///
    /// # Specification
    /// - requires: `top` names a top-level module of the collection.
    /// - ensures: one held slot at the top level, at the next admission
    ///   position, carries [`LoweringRefusal::ShadowedBuiltin`] at the module's
    ///   name; a `top` the collection does not hold appends nothing.
    /// - provides: the shadowing refusal [`Self::declare`] and
    ///   [`Self::declare_module`] share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module and a functor named as a builtin under the
    ///   reject policy are each refused at their name.
    /// - witness: `gandr-surface-lowering::tests::recognition::a_module_or_functor_shadowing_a_builtin_is_rejected_under_policy`
    #[spec(
        captures: before = self.cx().collected.slots.len(),
        ensures: self.cx().collected.slots.len() <= before.saturating_add(1)
            && self.cx().collected.slots.get(before).is_none_or(|slot| slot.role == Role::Held && matches!(slot.refusal, Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. })))),
    )]
    fn refuse_shadowing(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.cx().collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named, declared_by) = (module.name, module.named, module.declared_by);
        let held = SlotIndex::from(self.cx().collected.slots.len());
        let mut slot = DeclarationSlot {
            name,
            container: self.cx().collected.top(named.span.start()),
            role: Role::Held,
            constant: ConstantIndex::from(usize::from(held)),
            introduced_by: declared_by,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        };
        slot.refuse(declared_by.node, LoweringRefusal::ShadowedBuiltin {
            span: named.span,
            name,
        });
        self.cx_mut().collected.slots.push(slot);
    }

    /// Report the binder `binder`, spelling `name` and extending `frame`,
    /// against the outermost scope, and keep the binding it hides.
    ///
    /// # Specification
    /// - requires: `binder` is a written binder's name, and `frame` the frame
    ///   the binder extends.
    /// - ensures: a binder over a builtin root is recorded under
    ///   warn-and-allow; one [`Shadow`] of `binder`'s span and the binding
    ///   [`Self::hidden_by`] finds is pushed into the form the lowering reads,
    ///   and nothing when it finds none; the outermost scope and the reached
    ///   imports are never changed.
    /// - provides: the binder half of the outermost report, and the entries of
    ///   [`LoweredModule::shadows`].
    /// - fails: [`LoweringRefusal::ShadowedBuiltin`] at the binder for a
    ///   builtin root under the reject policy; propagates
    ///   [`LoweringRefusal::BudgetExceeded`] from the lookup.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ShadowedBuiltin`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda binder over a builtin under each policy,
    ///   asserted as the exact record and outcome; the shadows as
    ///   [`Self::hidden_by`] finds them.
    /// - witness: `gandr-surface-lowering::tests::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `gandr-surface-lowering::tests::scopes::each_shadowing_binder_keeps_the_binding_it_hides_6270`
    #[spec(
        captures: before = self.cx().shadows.entries().len(),
        ensures: |ret| {
            (ret.is_ok() && self.cx().shadows.entries().len() <= before.saturating_add(1))
                || ret
                    == Err(LoweringRefusal::ShadowedBuiltin {
                        span: binder.span,
                        name,
                    })
                || matches!(ret, Err(LoweringRefusal::BudgetExceeded { .. }))
        },
    )]
    #[inline]
    pub fn note_binder(
        &mut self,
        binder: Placed,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let noted = self
            .cx_mut()
            .recognition
            .note_binder(Segment::from(name.as_ref()), binder.span);
        let Ok(root) = noted
        else {
            return Err(LoweringRefusal::ShadowedBuiltin {
                span: binder.span,
                name,
            });
        };
        if let Maybe::Present(hidden) = self.hidden_by(binder, frame, name, root)? {
            let _place = self.cx_mut().shadows.push(Shadow {
                binder: binder.span,
                hidden,
            });
        }

        Ok(())
    }

    /// Read every declaration's operands at the sort the declaration demands.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: a signature's type is read as a value type, a definition's
    ///   body as a value in the outermost frame, a function tail's declaration
    ///   form as a function, which reads both halves it wrote at once, a
    ///   manifest type component's and a type member's type and an abstract
    ///   component's written kind as value types, a data declaration's
    ///   parameter types, universe and field types as value types under the
    ///   parameters before them, and an attribute's payload, a declaration's or
    ///   a decorated module's, as a value when its form can stand as one and
    ///   its schema is not a word schema, whose payload is read as written; a
    ///   witness's body, a member rather than a form, is read nowhere, nor is
    ///   either half of the prelude's `Eq.generic` ([`Role::Generic`]), which
    ///   names the derivation and lowers to nothing. Every other node stays
    ///   unread. Every written payload is marked as one, whatever its form, and
    ///   every signature type's root with the type components it sees. A
    ///   definition both of whose halves are written is signed as
    ///   `Native::sign_definitions` signs it.
    /// - provides: the entry points of the ascending sweep.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a payload of a mold the
    ///   grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] for a foreign mold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures and definitions seed different readings;
    ///   manifest types and attribute payloads retain their own roots,
    ///   including attributes of refused declarations.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body visits every slot and each of its attributes; the check reads each attribute's payload flag once"
        )
    )]
    #[spec(
        captures: before = (usize::from(self.cx().readings.count()), usize::from(self.cx().payload.count()), usize::from(self.cx().scopes.count())),
        ensures: |ret| {
            usize::from(self.cx().readings.count()) == before.0
                && usize::from(self.cx().payload.count()) == before.1
                && usize::from(self.cx().scopes.count()) == before.2
                && (ret.is_err()
                    || self
                        .cx().collected
                        .slots
                        .iter()
                        .flat_map(|slot| slot.attributes.iter())
                        .chain(
                            self.cx().collected
                                .decorated
                                .iter()
                                .flat_map(|module| module.attributes.iter()),
                        )
                        .all(|attribute| match attribute.payload {
                            | Payload::Unwritten => true,
                            | Payload::Written(payload) => self
                                .cx().payload
                                .get(payload.node)
                                .is_none_or(|flag| flag.0),
                        }))
        },
    )]
    #[inline]
    pub fn seed(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seeds: Vec<(NodeIndex, Reading)> = Vec::new();
        let mut payloads: Vec<NodeIndex> = Vec::new();
        let from = self.cx().current;
        let mut members: Vec<NodeIndex> = Vec::new();
        for structure in self.cx().collected.structures.iter().skip(from.structures) {
            for stated in structure.types.iter().chain(&structure.type_members) {
                if let TypeMeaning::Manifest(defined) = stated.meaning {
                    members.push(defined.node);
                }
            }
            for record in &structure.stated_at {
                seeds.push((record.node, Reading::ValueType(Frame::Outermost)));
            }
        }
        for stated in self
            .cx()
            .collected
            .type_members_in(Container::TopLevel(from.source))
        {
            if let TypeMeaning::Manifest(defined) = stated.meaning {
                members.push(defined.node);
            }
        }
        let cx = self.cx_mut();
        for recorded in cx
            .collected
            .abstracts
            .range(SlotIndex::from(from.slots) ..)
            .map(|(_, recorded)| recorded)
        {
            if let Maybe::Present(kind) = recorded.kind {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
                let _fresh = cx.kinds.insert(kind.node);
            }
        }
        for component in cx
            .collected
            .functors
            .iter()
            .skip(from.functors)
            .flat_map(|functor| functor.components.iter())
        {
            if let ParameterForm::Abstract(Maybe::Present(kind)) = component.form {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
                let _fresh = cx.kinds.insert(kind.node);
            }
        }
        for &(root, seen) in cx.collected.scopes.iter().skip(from.scopes) {
            if let Some(held) = cx.scopes.get_mut(root) {
                *held = Maybe::Present(seen);
            }
        }
        for &defined in &members {
            let _reading = Models::new(self.host()).member_reading(defined, Frame::Outermost)?;
        }
        for slot in self.cx().collected.slots.iter().skip(from.slots) {
            if slot.role == Role::Generic {
                continue;
            }
            if let Maybe::Present(half) = slot.signature
                && let Operand::Written(operand) = half.operand
            {
                seeds.push((operand.node, Reading::ValueType(Frame::Outermost)));
            }
            if let Maybe::Present(half) = slot.definition {
                match half.operand {
                    Operand::Written(operand) => {
                        seeds.push((operand.node, Reading::Value(Frame::Outermost)));
                    },
                    Operand::Function => {
                        seeds.push((half.declaration.node, Reading::Function));
                    },
                    Operand::Member(_)
                    | Operand::Data(_)
                    | Operand::Words(_)
                    | Operand::Terms(_)
                    | Operand::Loop { .. }
                    | Operand::Operation
                    | Operand::Derived
                    | Operand::Signature
                    | Operand::Presented
                    | Operand::Code
                    | Operand::Model(_)
                    | Operand::World => {},
                }
            }
        }
        let written = self
            .cx()
            .collected
            .slots
            .iter()
            .skip(from.slots)
            .flat_map(|slot| slot.attributes.iter())
            .chain(
                self.cx()
                    .collected
                    .decorated
                    .iter()
                    .skip(from.decorated)
                    .flat_map(|module| module.attributes.iter()),
            );
        for attribute in written {
            let Payload::Written(payload) = attribute.payload
            else {
                continue;
            };
            payloads.push(payload.node);
            payloads.extend(attribute.key.map(|key| key.node));
            // A named payload is never a value: its schema reads its spelling,
            // or refuses it.
            let worded = attribute.key.is_some()
                || matches!(
                    AttributeRegistry::lookup(attribute.name),
                    Maybe::Present((_, AttributeSchema::Word(_) | AttributeSchema::Spelled))
                );
            let (_shape, value) = self.shared().payload_former(payload)?;
            if value.0 && !worded {
                seeds.push((payload.node, Reading::Value(Frame::Outermost)));
            }
        }
        Native::new(self.host()).seed_data(&mut seeds);
        Models::new(self.host()).seed_families(&mut seeds)?;
        for defined in members {
            let reading = Models::new(self.host()).member_reading(defined, Frame::Outermost)?;
            seeds.push((defined, reading));
        }
        self.seed_descriptions(&mut seeds)?;
        Native::new(self.host()).sign_definitions()?;
        for (position, reading) in seeds {
            self.read(position, reading);
        }
        let repaired: Vec<NodeIndex> = self
            .cx()
            .collected
            .slots
            .iter()
            .skip(from.slots)
            .filter_map(|slot| match slot.refusal {
                Maybe::Present((
                    position,
                    LoweringRefusal::MalformedForm {
                        fault: FormFault::Repaired(_),
                        ..
                    },
                )) => Some(position),
                Maybe::Present(_) | Maybe::Absent(_) => None,
            })
            .collect();
        for position in repaired {
            self.repaired_calls(position);
        }
        for position in payloads {
            if let Some(held) = self.cx_mut().payload.get_mut(position) {
                *held = InPayload(true);
            }
        }

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The form a payload is written as, and whether it can stand as a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a known form yields its classification and value-form
    ///   verdict; a missing node yields layout and a negative verdict.
    /// - fails: with an unknown-mold refusal when the grammar cannot classify
    ///   the node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value and non-value payloads take distinct schema
    ///   paths while every eligible former is covered by the value-form
    ///   classification table.
    /// - witness: `gandr-surface-lowering::lower::tests::only_the_value_forms_can_stand_as_a_payload`
    /// - witness: `gandr-surface-lowering::lower::tests::a_non_value_payload_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        ensures: |ret| {
            ret == self.cx().tree.node(payload.node).map_or(
                Ok((Shape::Layout, ValueForm(false))),
                |node| {
                    shape_of(self.cx().pbg, node).map(|shape| {
                        (shape, match shape {
                            | Shape::Form { former, .. } => is_value_form(former),
                            | Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
                        })
                    })
                },
            )
        },
    )]
    fn payload_former(
        &self,
        payload: Placed,
    ) -> Result<(Shape, ValueForm), LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(payload.node)
        else {
            return Ok((Shape::Layout, ValueForm(false)));
        };
        let shape = shape_of(self.cx().pbg, node)?;
        let value = match shape {
            Shape::Form { former, .. } => is_value_form(former),
            Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
        };

        Ok((shape, value))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The ascending sweep: classify every read node and plan its mint.
    ///
    /// # Specification
    /// - requires: the seeds have been read.
    /// - ensures: every node carries the reading its parent fixed, the owner
    ///   its parent belongs to and its parent's payload mark, every read form
    ///   has its plan or has offered its refusal to the declaration that owns
    ///   it, and a node under a form that refused stays unread, so a refusal
    ///   costs its subtree nothing.
    /// - provides: everything the mint sweep needs, so the mint sweep decides
    ///   nothing and can fail at nothing.
    /// - fails: every engine fault — [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] — aborts the sweep; every other
    ///   refusal is offered to its declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration refusals remain local while grammar and
    ///   budget faults abort the run; classification spends at least one step
    ///   per source node and does not allocate declaration slots.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tree_of_another_grammar_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_past_the_allowance_is_refused`
    #[spec(
        captures: before = (
            usize::from(self.cx().fuel.remaining()),
            self.cx().collected.slots.len(),
            self.cx().plans.count(),
        ),
        ensures: |ret| {
            self.cx().collected.slots.len() == before.1
                && self.cx().plans.count() == before.2
                && usize::from(self.cx().fuel.remaining()) <= before.0
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || usize::from(self.cx().fuel.remaining())
                        <= before.0.saturating_sub(self.cx().own.len()))
        },
    )]
    #[inline]
    pub fn classify(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        for index in 0 .. self.cx().own.len() {
            let Some(&position) = self.cx().own.get(index)
            else {
                continue;
            };
            self.cx_mut().fuel.spend()?;
            if self.cx().classified_ahead.contains(&position) {
                continue;
            }
            self.classify_one(position)?;
            while let Some(next) = self.cx_mut().ahead.pop() {
                if self.cx_mut().classified_ahead.insert(next) {
                    self.classify_one(next)?;
                }
            }
        }

        Ok(())
    }

    /// Push the binder frames and the flat stores' entries after this into
    /// `form`, the layout block of the form whose node the lowering reads
    /// now.
    ///
    /// # Specification
    /// trivial.
    fn enter(
        &mut self,
        form: LayoutBlock,
    )
    {
        self.cx_mut().scope.enter(form);
        self.cx_mut().operands.enter(form);
        self.cx_mut().else_ifs.enter(form);
        self.cx_mut().segments.enter(form);
        self.cx_mut().statements.enter(form);
        self.cx_mut().parameters.enter(form);
        self.cx_mut().endpoints.enter(form);
        self.cx_mut().cases.enter(form);
        self.cx_mut().arms.enter(form);
        self.cx_mut().projected.enter(form);
        self.cx_mut().shadows.enter(form);
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The positions of the operands that the key `kept` names, for a read
    /// that walks them by position; no position for a key the store does not
    /// hold whole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn spread(
        &self,
        kept: FormStretch,
    ) -> Stretch
    {
        let start = self.cx().operands.first(kept).map_or(0_usize, usize::from);
        Stretch {
            start,
            end: start.saturating_add(self.cx().operands.read(kept).len()),
        }
    }

    /// The reason that the first operand of `kept` holds when `read` answers
    /// it absent; `None` when `read` answers every operand present.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: reads each operand of the one stretch a mint consumes once, as
    ///   the mint itself does; no read grows with the module.
    fn first_absent<Held, Read>(
        &self,
        kept: FormStretch,
        read: Read,
    ) -> Option<lowered::Absent>
    where
        Read: Fn(NodeIndex) -> Maybe<Held, lowered::Absent>,
    {
        self.cx()
            .operands
            .read(kept)
            .iter()
            .find_map(|&operand| match read(operand) {
                Maybe::Present(_) => None,
                Maybe::Absent(reason) => Some(reason),
            })
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Hand `position`'s records to its children and classify it, offering a
    /// refusal to its declaration, its frames pushed into its form.
    ///
    /// # Specification
    /// - requires: `position` is reached in ascending arena order, or asked
    ///   ahead by the form it stands under, so the records the sweep hands down
    ///   have reached it.
    /// - ensures: `position`'s children carry its records, and it is planned or
    ///   its refusal offered to it; every frame it pushes takes its place in
    ///   [`Context::form_of`] `position`.
    /// - provides: the per-position step of [`Self::classify`].
    /// - fails: an engine fault, on which [`Self::classify`] aborts.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration refusals remain local while grammar and
    ///   budget faults abort the run; a manifest model type's application,
    ///   asked ahead, is planned before a later parameter reads a sort the type
    ///   leaves a field.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_sort_a_partly_manifest_type_leaves_a_field_is_read_off_its_binder_2158`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault))]
    fn classify_one(
        &mut self,
        position: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.enter(self.cx().form_of(position));
        self.inherit_owner(position);
        self.inherit_payload(position);
        self.inherit_scope(position);
        self.inherit_type(position);
        self.inherit_scrutiny(position);
        if let Err(refusal) = self.classify_node(position) {
            if refusal.classify() == FailureClass::EngineFault {
                return Err(refusal);
            }
            if let LoweringRefusal::UnresolvedName { span, .. } = refusal {
                self.cx_mut().unresolved.push((position, span));
            }
            self.cx_mut().collected.offer(position, refusal);
        }

        Ok(())
    }

    /// Give every child of `position` the match on a recursive function's
    /// parameter `position` stands under, unless a match of its own records
    /// one.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   record is set when its children are reached; a match records its arm
    ///   bodies when it is classified, after this hands its own record down.
    /// - ensures: every child of a recorded node carries a record, its own when
    ///   it had one and its parent's otherwise; a node under several such
    ///   matches carries the innermost's.
    /// - provides: the scrutiny a claim reads, however deep under its arm.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a claim nested in a call, a constructor and a
    ///   statement under an arm reads its match's record; under two nested
    ///   matches, the inner one's.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    /// - witness: `gandr-surface-lowering::lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
    #[spec(
        captures: before = self.cx().scrutinised.get(&position).copied(),
        ensures: |_| {
            self.cx().scrutinised.get(&position).copied() == before
                && before.is_none_or(|_| self.cx().tree.children(position).all(|child| self.cx().scrutinised.contains_key(&child)))
        },
    )]
    fn inherit_scrutiny(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&seen) = self.cx().scrutinised.get(&position)
        else {
            return;
        };
        for child in self.cx().tree.children(position) {
            let _held = self.cx_mut().scrutinised.entry(child).or_insert(seen);
        }
    }

    /// Give every unowned child of `position` the declaration its parent
    /// belongs to.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   owner is already set when its children are reached.
    /// - ensures: every child of an owned node is owned by the same slot,
    ///   unless the collection pass gave it an owner of its own — a signature
    ///   type written inside a member signature it does not type — so a refusal
    ///   anywhere under a declaration reaches the declaration its type or body
    ///   belongs to. Under an application spine `f x y`, which is read as the
    ///   pieces of one call, each application down its left side and each
    ///   argument's group also give their children that slot, because the
    ///   spine's reader reads them as no forms of their own.
    /// - provides: the ownership half of the one-refusal-per-declaration rule.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal and payload nodes remain owned by the correct
    ///   declaration, including payloads lowered after their declaration is
    ///   refused.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_argument_and_an_inferring_call_lower_4853`
    #[spec(
        captures: before = (
            usize::from(self.cx().collected.owner.count()),
            self.cx().collected.owner_of(position),
        ),
        ensures: |_| {
            usize::from(self.cx().collected.owner.count()) == before.0
                && self.cx().collected.owner_of(position) == before.1
                && (!matches!(before.1, Maybe::Present(_))
                    || self
                        .cx().tree
                        .children(position)
                        .all(|child| matches!(self.cx().collected.owner_of(child), Maybe::Present(_))))
        },
    )]
    #[inline]
    pub fn inherit_owner(
        &mut self,
        position: NodeIndex,
    )
    {
        let Maybe::Present(slot) = self.cx().collected.owner_of(position)
        else {
            return;
        };
        self.own_children(position, slot);
        // A juxtaposed spine of either sort spells one call, so its operands
        // take the slot its outermost application takes.
        let Some(application) = self
            .cx()
            .tree
            .node(position)
            .and_then(|node| match node.label() {
                NodeLabel::Meld(mold)
                    if Some(mold) == self.cx().pbg.application()
                        || Some(mold)
                            == self
                                .cx()
                                .pbg
                                .application_in(gandr_surface_grammar::Sort::Type) =>
                {
                    Some(mold)
                },
                NodeLabel::Meld(_)
                | NodeLabel::Tile(_)
                | NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc => None,
            })
        else {
            return;
        };
        let mut spine = position;
        while self
            .cx()
            .tree
            .node(spine)
            .is_some_and(|node| node.label() == NodeLabel::Meld(application))
        {
            let mut parts = self.cx().tree.children(spine).filter(|&child| {
                self.cx()
                    .tree
                    .node(child)
                    .is_some_and(|node| !matches!(node.label(), NodeLabel::Space | NodeLabel::Doc))
            });
            let (Some(left), Some(_tile), Some(right)) = (parts.next(), parts.next(), parts.next())
            else {
                return;
            };
            self.own_children(left, slot);
            self.own_children(right, slot);
            spine = left;
        }
    }

    /// Give every unowned child of `position` the slot `slot`.
    ///
    /// # Specification
    /// trivial.
    fn own_children(
        &mut self,
        position: NodeIndex,
        slot: SlotIndex,
    )
    {
        for child in self.cx().tree.children(position) {
            if let Maybe::Absent(_) = self.cx().collected.owner_of(child) {
                self.cx_mut().collected.own(child, slot);
            }
        }
    }

    /// Give every unowned node written at `written` the declaration `anchor`
    /// belongs to, ahead of the walk.
    ///
    /// # Specification
    /// - requires: `written` is `anchor` or a node under it, so the walk would
    ///   give it `anchor`'s owner.
    /// - ensures: when `anchor` is owned, every node under `written`, itself
    ///   included, that had no owner has `anchor`'s; nothing else changes.
    /// - provides: the owner a name resolves by where it is read before the
    ///   walk reaches it: a lambda reads its binder's type, and a bare lambda's
    ///   signature lies after its body in the arena; a selection reads the name
    ///   its chain of selections ends at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare lambda signed `+U (Empty -> -F Integer)`
    ///   matches no arm on its binder where its signature lies after its body;
    ///   a field of a field reads the record its chain begins at.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_bare_signed_lambda_s_binder_is_typed_as_in_its_thunk_1944`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_field_of_a_record_no_type_states_projects_its_label_1106`
    #[spec(
        captures: before = (
            usize::from(self.cx().collected.owner.count()),
            self.cx().collected.owner_of(anchor),
        ),
        ensures: |_| usize::from(self.cx().collected.owner.count()) == before.0
            && self.cx().collected.owner_of(anchor) == before.1,
    )]
    #[inline]
    pub fn own_written(
        &mut self,
        written: NodeIndex,
        anchor: NodeIndex,
    )
    {
        let Maybe::Present(slot) = self.cx().collected.owner_of(anchor)
        else {
            return;
        };
        let mut nodes = alloc::vec![written];
        while let Some(node) = nodes.pop() {
            if let Maybe::Absent(_) = self.cx().collected.owner_of(node) {
                self.cx_mut().collected.own(node, slot);
            }
            nodes.extend(self.cx().tree.children(node));
        }
    }

    /// Give every child of `position` the manifest type components `position`
    /// sees.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   scope is already set when its children are reached.
    /// - ensures: every node under a signature type's root sees that root's
    ///   manifest components, an inner root keeping its own.
    /// - provides: the scope a type head inside a signature resolves against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — manifest names in later component types resolve
    ///   through the enclosing signature prefix rather than ambient source
    ///   declarations.
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = (
            usize::from(self.cx().scopes.count()),
            self.cx().scopes.get(position).copied(),
        ),
        ensures: |_| {
            usize::from(self.cx().scopes.count()) == before.0
                && self.cx().scopes.get(position).copied() == before.1
                && (!matches!(before.1, Some(Maybe::Present(_)))
                    || self.cx().tree.children(position).all(|child| {
                        self.cx().scopes
                            .get(child)
                            .is_none_or(|scope| matches!(*scope, Maybe::Present(_)))
                    }))
        },
    )]
    fn inherit_scope(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&Maybe::Present(seen)) = self.cx().scopes.get(position)
        else {
            return;
        };
        for child in self.cx().tree.children(position) {
            if let Some(held) = self.cx_mut().scopes.get_mut(child)
                && let Maybe::Absent(_) = *held
            {
                *held = Maybe::Present(seen);
            }
        }
    }

    /// Mark every child of `position` as standing inside a type, inside a type
    /// a body quotes, and at an endpoint, when `position` does.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   marks are already set when its children are reached.
    /// - ensures: every node under a path type's endpoint carries both marks,
    ///   and every node under reflexivity's point the endpoint mark, before it
    ///   is classified.
    /// - provides: the context a bound name inside a type resolves in, and the
    ///   one a computation standing as a value is returned in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter named inside a compound endpoint of the
    ///   result type binds dependently and is read at its telescope index, and
    ///   a call nested in an endpoint's argument is returned.
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        captures: marked = (self.cx().in_type.contains(&position), self.cx().at_endpoint.contains(&position)),
        ensures: |_| {
            self.cx().in_type.contains(&position) == marked.0
                && self.cx().at_endpoint.contains(&position) == marked.1
                && (!marked.0 || self.cx().tree.children(position).all(|child| self.cx().in_type.contains(&child)))
                && (!marked.1 || self.cx().tree.children(position).all(|child| self.cx().at_endpoint.contains(&child)))
        },
    )]
    fn inherit_type(
        &mut self,
        position: NodeIndex,
    )
    {
        let cx = self.cx_mut();
        if cx.in_type.contains(&position) {
            cx.in_type.extend(cx.tree.children(position));
        }
        if cx.in_quote.contains(&position) {
            cx.in_quote.extend(cx.tree.children(position));
        }
        if cx.at_endpoint.contains(&position) {
            cx.at_endpoint.extend(cx.tree.children(position));
        }
    }

    /// Mark every child of `position` as inside a payload when `position` is.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   mark is already set when its children are reached.
    /// - ensures: every node under a written payload carries the mark, so the
    ///   mint sweep can tell a payload's subtree from the rest of its
    ///   declaration.
    /// - provides: the payload half of what the mint sweep skips.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration still mints its attribute
    ///   payload without minting the refused signature or body, a compound
    ///   payload down to its leaves.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_compound_payload_is_lowered_to_its_leaves`
    #[spec(
        captures: before = (usize::from(self.cx().payload.count()), self.shared().in_payload(position)),
        ensures: |_| {
            usize::from(self.cx().payload.count()) == before.0
                && self.shared().in_payload(position) == before.1
                && (!before.1.0
                    || self.cx().tree.children(position).all(|child| {
                        self.cx().payload
                            .get(child)
                            .is_none_or(|flag| flag.0)
                    }))
        },
    )]
    fn inherit_payload(
        &mut self,
        position: NodeIndex,
    )
    {
        if !self.shared().in_payload(position).0 {
            return;
        }
        for child in self.cx().tree.children(position) {
            if let Some(held) = self.cx_mut().payload.get_mut(child) {
                *held = InPayload(true);
            }
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Whether `position` lies inside an attribute payload.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored payload flag; an
    ///   out-of-range position is outside every payload.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refused declarations keep payload interpretation
    ///   separate from their signature and body.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .cx().payload
                    .get(position)
                    .is_some_and(|flag| flag.0)
        },
    )]
    fn in_payload(
        &self,
        position: NodeIndex,
    ) -> InPayload
    {
        self.cx()
            .payload
            .get(position)
            .copied()
            .unwrap_or(InPayload(false))
    }

    /// Whether `position` is a type a module signature states, read in that
    /// signature's scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly when the position holds a signature
    ///   scope; an out-of-range position holds none.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused member's stated type is minted while its
    ///   body is not.
    /// - witness: `gandr-surface-lowering::lower::tests::a_signature_s_types_answer_whatever_its_members_1115`
    #[spec(ensures: |ret| ret.0 == matches!(self.cx().scopes.get(position), Some(&Maybe::Present(_))))]
    fn stated_apart(
        &self,
        position: NodeIndex,
    ) -> StatedApart
    {
        StatedApart(matches!(
            self.cx().scopes.get(position),
            Some(&Maybe::Present(_))
        ))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify one node at the reading its parent fixed.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, or asked
    ///   ahead by the form it stands under, as [`Self::classify_one`] reaches
    ///   it.
    /// - ensures: an unread node, an own tile, layout and repairs are skipped;
    ///   a read form is checked in the crate's one order and either planned,
    ///   with its operands read at the sorts it demands, or refused.
    /// - provides: the per-node half of [`Self::classify`].
    /// - fails: yields the form's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read form gets its own plan or a located refusal;
    ///   unread source and grammar faults are not mistaken for admitted terms.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_repaired_declaration_is_refused`
    #[spec(
        captures: active = self.cx().reading(position) != Reading::Unread
            && self
                .cx().tree
                .node(position)
                .is_some_and(|node| matches!(shape_of(self.cx().pbg, node), Ok(Shape::Form { .. }))),
        ensures: |ret| {
            (!active
                || ret.is_err()
                || self
                    .cx().plans
                    .get(position)
                    .is_some_and(|plan| *plan != Plan::Unplanned))
                && (self.cx().reading(position) != Reading::Unread || ret.is_ok())
        },
    )]
    fn classify_node(
        &mut self,
        position: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let reading = self.cx().reading(position);
        if reading == Reading::Unread {
            return Ok(());
        }
        let Some(node) = self.cx().tree.node(position)
        else {
            return Ok(());
        };
        let Shape::Form { name, former } = shape_of(self.cx().pbg, node)?
        else {
            return Ok(());
        };
        let site = Site {
            at: Placed::of(position, node),
            name,
            reading,
        };
        if let Former::Unadmitted(feature) = former {
            return Err(site.out(FragmentBoundary::Unadmitted(feature)));
        }
        if let Former::Reserved(feature) = former {
            return Err(site.out(FragmentBoundary::Reserved(feature)));
        }
        if former == Former::Misplaced {
            return Err(site.out(FragmentBoundary::Misplaced));
        }
        let mut pieces = core::mem::take(&mut self.cx_mut().pieces);
        // A value standing inside a type reads its own operands inside it too.
        self.cx_mut().reader =
            if self.cx().type_read.contains(&position) || self.cx().in_type.contains(&position) {
                Reading::ValueType(reading.frame())
            }
            else {
                reading
            };
        let outcome = read_pieces(self.cx().pbg, self.cx().tree, position, &mut pieces)
            .and_then(|()| self.classify_form(site, former, &pieces));
        self.cx_mut().reader = Reading::Unread;
        self.cx_mut().pieces = pieces;

        outcome
    }

    /// Classify one read form over its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form at `site`.
    /// - ensures: a repair refuses the form; a former of the wrong family for
    ///   the position refuses as the wrong sort, at the outermost grouping
    ///   around it ([`Self::standing`](crate::lower::ExpressionsRef::standing)),
    ///   except a type standing where a value is read, which is quoted, and a
    ///   term name or a capitalised name standing where a type is read, which
    ///   is read as the type head of that spelling, and a call standing where a
    ///   type is read, which is read as the type application it spells; a
    ///   block's last computation written as a statement that is not an exit
    ///   and does not leave on every path is recorded as trailing, not where a
    ///   path ends; a form where a body ends that is neither an exit nor a form
    ///   that passes the end on — a block, a match, a grouping — nor a hole
    ///   takes the exit its polarity names, recorded as inferred and leaving,
    ///   and is handed to its reader; every other former is handed to its own
    ///   reader, a declaration form to the function reader, the one reading of
    ///   the family that seeds one.
    /// - provides: the dispatch on the grammar's named kind.
    /// - fails: yields the form's first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repairs take precedence over admission, wrong
    ///   families are refused, a type read as a value is the explicit quoting
    ///   exception, a computation read as a value is nested, and a tail of each
    ///   polarity takes its inferred exit.
    /// - witness: `gandr-surface-lowering::lower::tests::a_repaired_declaration_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouped_form_of_the_wrong_sort_is_refused_at_its_parentheses_2341`
    #[spec(
        ensures: |ret| {
            if let Maybe::Present(repaired) = pieces.repair {
                ret == Err(repaired.refusal(site.name))
            }
            else if family_of(former) != site.reading.family()
                && !(family_of(former) == Family::Type && matches!(site.reading, Reading::Value(_)))
                && !(matches!(former, Former::Name | Former::Constructor) && site.reading.family() == Family::Type)
                && !(former == Former::Call && site.reading.family() == Family::Type)
            {
                ret == Err(self.shared().standing(site).out(FragmentBoundary::WrongSort))
            }
            else if self.cx().exits.contains(&site.at.node) && ending(former) == Ending::Inferred {
                self.cx().inferred.contains(&site.at.node) && self.cx().leaving.contains(&site.at.node)
                    && (ret.is_err()
                        || self
                            .cx().plans
                            .get(site.at.node)
                            .is_some_and(|plan| *plan != Plan::Unplanned))
            }
            else {
                ret.is_err()
                    || self
                        .cx().plans
                        .get(site.at.node)
                        .is_some_and(|plan| *plan != Plan::Unplanned)
            }
        },
    )]
    fn classify_form(
        &mut self,
        site: Site,
        former: Former,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(site.name));
        }
        let family = family_of(former);
        let quoted = family == Family::Type && matches!(site.reading, Reading::Value(_));
        let headed = matches!(former, Former::Name | Former::Constructor)
            && site.reading.family() == Family::Type;
        if family != site.reading.family()
            && !quoted
            && !(site.reading.family() == Family::Type && read_as_type(former).0)
        {
            return Err(self
                .shared()
                .standing(site)
                .out(FragmentBoundary::WrongSort));
        }
        // A block's last statement that is not an exit runs, its result
        // discarded, and the block returns the unit after it.
        if self.cx().stated.contains_key(&site.at.node)
            && ending(former) != Ending::Exit
            && !self.cx().iterated.contains(&site.at.node)
        {
            Exits::new(self.host()).trail(site);
        }
        if self.cx().exits.contains(&site.at.node) && ending(former) == Ending::Inferred {
            let _tail = self.cx_mut().inferred.insert(site.at.node);
            let _exit = self.cx_mut().leaving.insert(site.at.node);
        }
        if self.cx().iterated.contains(&site.at.node)
            && ending(former) != Ending::Exit
            && (self.cx().stated.contains_key(&site.at.node)
                || iterating(former) == Ending::Inferred)
        {
            Exits::new(self.host()).reenter(site)?;
        }
        if let Some(&assignment) = self.cx().assignments.get(&site.at.node) {
            return Capability::new(self.host()).assign(site, former, pieces, assignment);
        }
        let cursor = Cursor::new(&pieces.pieces, site.at.span);
        match former {
            Former::Name | Former::Constructor if headed => self.type_head(site, cursor),
            Former::Name => self.name(site),
            Former::Constructor => self.constructor(site, Some(cursor)),
            Former::Hole if site.name == FormName::SPLICE => self.splice(site, cursor),
            Former::Hole => {
                // A wildcard stands for a value the equations force; where a
                // computation is read it is a form of the wrong sort, since the
                // solver binds values only.
                let hole = if site.name == FormName::WILDCARD {
                    if matches!(site.reading, Reading::Computation(_) | Reading::Head(_)) {
                        return Err(site.out(FragmentBoundary::WrongSort));
                    }
                    self.nominate(implicit::Nomination::Wildcard)?
                }
                else {
                    self.hole(site.at)?
                };
                let plan = if matches!(site.reading, Reading::Computation(_) | Reading::Head(_)) {
                    let _frame = self.require(site, Produced::Computation)?;
                    Plan::CompHole(hole)
                }
                else {
                    let _frame = self.require(site, Produced::Value)?;
                    Plan::ValueHole(hole)
                };
                self.plan(site, plan);
                Ok(())
            },
            Former::Number => self.number(site),
            Former::Boolean => {
                let _frame = self.require(site, Produced::Value)?;
                let side = if self.cx().text_at(site.at).as_ref() == "true" {
                    gandr_kernel_term::Side::Left
                }
                else {
                    gandr_kernel_term::Side::Right
                };
                self.plan(site, Plan::Boolean(side));
                Ok(())
            },
            Former::Text => self.text(site, pieces),
            Former::Character => self.character(site),
            Former::Parenthesized => self.parenthesized(site, cursor),
            Former::TypeQuote => self.type_quote(site, cursor),
            Former::Thunk => self.thunk(site, cursor),
            Former::Lambda => self.lambda(site, cursor),
            Former::Block => self.sequenced(site, cursor),
            Former::Return => self.keyed(site, cursor, TileName::PURE),
            Former::Exit => self.keyed(site, cursor, TileName::RETURN),
            Former::Become => self.tail_call(site, cursor),
            Former::Loop => Exits::new(self.host()).looped(site, cursor),
            Former::While => Exits::new(self.host()).repeated(site, cursor),
            Former::For => Exits::new(self.host()).stepped(site, cursor),
            Former::Break => Exits::new(self.host()).broken(site, cursor),
            Former::Continue => Exits::new(self.host()).continued(site, cursor),
            Former::Force => self.keyed(site, cursor, TileName::FORCE),
            Former::Run => self.run(site, cursor),
            Former::Call => self.call(site, cursor),
            Former::Case => Native::new(self.host()).case(site, cursor),
            Former::If => self.conditional(site, cursor),
            Former::Telescope => Models::new(self.host()).telescope(site, cursor),
            Former::List => self.list(site, cursor),
            Former::PackModel => Models::new(self.host()).pack_model(site, cursor),
            Former::ForgetModel => Models::new(self.host()).forget_model(site, cursor),
            Former::Injection => Models::new(self.host()).injection(site, cursor),
            Former::LazyRecord => Models::new(self.host()).copattern(site, cursor),
            Former::Binary | Former::Unary => self.operator(site, pieces),
            Former::Projection => self.projection(site, pieces),
            Former::TypeHead => self.type_head(site, cursor),
            Former::TypePath => self.type_path(site, pieces),
            Former::Universe => self.universe(site, cursor),
            Former::TypeApplication => self.type_application(site, cursor),
            Former::ThunkType | Former::ReturnerType => self.formed_type(site, cursor),
            Former::ArrowType => self.arrow(site, cursor),
            Former::LinearArrowType => Models::new(self.host()).linear_arrow(site, cursor),
            Former::ProductType => self.chain(site, cursor, Former::ProductType),
            Former::SumType => self.chain(site, cursor, Former::SumType),
            Former::LazyProductType => self.chain(site, cursor, Former::LazyProductType),
            Former::TelescopeType => Models::new(self.host()).telescope_type(site, cursor),
            Former::LabelledSumType => Models::new(self.host()).labelled_sum_type(site, cursor),
            Former::LazyRecordType => Models::new(self.host()).lazy_record_type(site, cursor),
            Former::ParenthesizedType => self.parenthesized_type(site, cursor),
            Former::PathType => {
                Identities::new(self.host()).path_type(site, cursor, Relating::Path)
            },
            Former::BridgeType => {
                Identities::new(self.host()).path_type(site, cursor, Relating::Bridge)
            },
            Former::FlowType => Identities::new(self.host()).supplied_flow(site, cursor),
            Former::RelationType => Identities::new(self.host()).relation_type(site, cursor),
            Former::ManifestType => Models::new(self.host()).manifest_model(site, cursor),
            Former::CapabilityType => Capability::new(self.host()).capability_type(site, cursor),
            Former::AtType => Capability::new(self.host()).at_type(site, cursor),
            Former::StagedType => self.staged_type(site, cursor),
            Former::ModedType => CapabilityRef::new(self.host_ref()).moded_type(site, cursor),
            Former::Scope => Capability::new(self.host()).capability_scope(site, pieces),
            Former::Instantiation => Native::new(self.host()).instantiation(site, cursor),
            Former::SessionType => Capability::new(self.host()).session_type(site),
            Former::Action | Former::Offer => {
                Capability::new(self.host()).session_action(site, cursor)
            },
            Former::Access => Capability::new(self.host()).access_form(site, pieces),
            Former::World => self.world_form(site, pieces),
            Former::Declaration | Former::Module => self.function(site, cursor),
            Former::AttributeBlock
            | Former::Visibility
            | Former::Import
            | Former::Data
            | Former::Mutual
            | Former::Reserved(_)
            | Former::WorldDeclaration
            | Former::Unadmitted(_)
            | Former::Misplaced => Err(site.out(FragmentBoundary::WrongSort)),
        }
    }

    /// Keep what the head of each call the parser closed for the source
    /// names, inside the declaration at `declaration` that the repair
    /// refuses: a call typed before its `)` keeps its head's referent, the
    /// `)` of a juxtaposed call's argument group among them.
    ///
    /// # Specification
    /// - requires: the declaration at `declaration` was refused for a repair it
    ///   holds.
    /// - ensures: every form the walk reaches inside it takes the declaration
    ///   as its owner where it had none; for every call inside it holding a `)`
    ///   the source never wrote, itself or in the group of its last argument,
    ///   whose head is a name that resolves where the module's declarations are
    ///   read, the resolution is kept at the name; nothing else changes.
    /// - provides: the head's use for an editor while the call is typed.
    /// - fails: never; a head that does not resolve is passed over.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call written up to its next argument without its
    ///   `)`, at the end of a definition the repair refuses; a head left
    ///   unresolved, or kept at the whole call, changes the resolutions.
    /// - witness: `gandr-surface-lowering::tests::scopes::an_unclosed_call_keeps_its_head_s_referent_843`
    #[spec(
        captures: before = (
            usize::from(self.cx().collected.owner.count()),
            self.cx().collected.owner_of(declaration),
        ),
        ensures: |_| usize::from(self.cx().collected.owner.count()) == before.0
            && self.cx().collected.owner_of(declaration) == before.1,
    )]
    fn repaired_calls(
        &mut self,
        declaration: NodeIndex,
    )
    {
        // economy: the walk runs only over a declaration the parser repaired,
        // so a clean tree never pays for it.
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let application = self.cx().pbg.application().map(NodeLabel::Meld);
        let ghost_paren = |tree: &SyntaxTree<'source>, at: NodeIndex| {
            tree.children(at).any(|child| {
                matches!(
                    tree.node(child).map(gandr_surface_syntax::Node::label),
                    Some(NodeLabel::GhostClose {
                        class: ClosingClass::Paren,
                        ..
                    })
                )
            })
        };
        let mut forms = alloc::vec![declaration];
        while let Some(form) = forms.pop() {
            // The walk never visited this declaration, so its nodes take their
            // owner here: a name resolves only where a declaration owns it.
            self.inherit_owner(form);
            let juxtaposed = application.is_some()
                && self
                    .cx()
                    .tree
                    .node(form)
                    .map(gandr_surface_syntax::Node::label)
                    == application;
            let mut unclosed = ghost_paren(self.cx().tree, form);
            for child in self.cx().tree.children(form) {
                if let Some(NodeLabel::Meld(_)) = self
                    .cx()
                    .tree
                    .node(child)
                    .map(gandr_surface_syntax::Node::label)
                {
                    forms.push(child);
                    // A juxtaposed call holds the `)` of its argument's group.
                    unclosed |= juxtaposed && ghost_paren(self.cx().tree, child);
                }
            }
            let call = unclosed
                && (juxtaposed
                    || self.cx().tree.node(form).is_some_and(|node| {
                        matches!(
                            shape_of(self.cx().pbg, node),
                            Ok(Shape::Form {
                                former: Former::Call,
                                ..
                            })
                        )
                    }));
            if !call || read_pieces(self.cx().pbg, self.cx().tree, form, &mut scratch).is_err() {
                continue;
            }
            let Some(&Piece::Operand(head)) = scratch.pieces.first()
            else {
                continue;
            };
            let named = self.cx().tree.node(head.node).is_some_and(|node| {
                matches!(
                    shape_of(self.cx().pbg, node),
                    Ok(Shape::Form {
                        former: Former::Name,
                        ..
                    })
                )
            });
            if !named {
                continue;
            }
            let name = self.cx().name_at(head);
            let site = Site {
                at: head,
                name: FormName::DECLARATION,
                reading: Reading::Value(Frame::Outermost),
            };
            if let Ok(Maybe::Present(resolved)) = self.resolve_name(site, Frame::Outermost, name) {
                self.resolved(head.span, resolved);
            }
        }
        self.cx_mut().scratch = scratch;
    }

    /// Record the tile at `position`, covering `span`, among the names the
    /// lowering refused as unresolved, when it is an identifier that reads as
    /// an operator written wrong ([`RunReading::Operator`]) and no declaration
    /// answers it where the module's declarations are read. The lowering never
    /// reaches a name that a repair stands before, so
    /// [`Self::record_runs_behind_repairs`] offers such a name here.
    ///
    /// # Specification
    /// - requires: the node that holds `position` has its owner.
    /// - ensures: `(position, span)` joins `self.cx().unresolved` exactly when
    ///   the tile is an identifier, its text is operator-shaped and the name
    ///   resolves to nothing; nothing else changes.
    /// - fails: never; a budget refusal records nothing.
    /// - panics: none.
    /// - executable: none — the clause restates the resolution.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `=>>` behind a repair, with no declaration of that
    ///   name, is recorded and then refused at the run.
    /// - witness: `gandr-surface-lowering::lower::tests::an_operator_near_miss_behind_a_zero_width_repair_is_refused_at_the_run_5512`
    fn record_unresolved_run(
        &mut self,
        position: NodeIndex,
        span: ByteSpan,
    )
    {
        let identifier = self.cx().tree.node(position).is_some_and(|node| {
            tile_label(self.cx().pbg, node) == Maybe::Present(TileName::IDENTIFIER)
        });
        let at = Placed {
            node: position,
            span,
        };
        if !identifier || run_reading(self.cx().text_at(at)) != RunReading::Operator {
            return;
        }
        let site = Site {
            at,
            name: FormName::DECLARATION,
            reading: Reading::Value(Frame::Outermost),
        };
        if let Ok(Maybe::Absent(_)) =
            self.resolve_name(site, Frame::Outermost, self.cx().name_at(at))
        {
            self.cx_mut().unresolved.push((position, span));
        }
    }

    /// Offer the tile that starts just after each zero-width refusal of a
    /// declaration of the current source, with only white space between, to
    /// [`Self::record_unresolved_run`]. A repair inside a body refuses the
    /// declaration while the body lowers, so the lowering never resolves a
    /// name after the repair.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: for each slot of the current source whose refusal is zero
    ///   width and inside a half, the tile inside that half that starts where
    ///   the white space after the refusal ends is offered; each node on the
    ///   way down to it takes the declaration as its owner where it had none;
    ///   nothing else changes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the descent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `=>>` of a match arm after the repair that stands
    ///   for its `=>` is offered and recorded.
    /// - witness: `gandr-surface-lowering::lower::tests::an_operator_near_miss_behind_a_zero_width_repair_is_refused_at_the_run_5512`
    fn record_runs_behind_repairs(&mut self)
    {
        let tree = self.cx().tree;
        // Only a zero-width refusal yields an entry, so a source whose
        // declarations all lower allocates nothing.
        let behind: Vec<(NodeIndex, ByteOffset)> = self
            .cx()
            .collected
            .slots
            .iter()
            .skip(self.cx().current.slots)
            .filter_map(|slot| {
                let Maybe::Present((_, ref refusal)) = slot.refusal
                else {
                    return None;
                };
                let Maybe::Present(refused) = refusal.span()
                else {
                    return None;
                };
                if refused.start() != refused.end() {
                    return None;
                }
                [slot.signature, slot.definition]
                    .into_iter()
                    .find_map(|half| match half {
                        Maybe::Present(half)
                            if half.declaration.span.start() <= refused.start()
                                && refused.end() <= half.declaration.span.end() =>
                        {
                            let rest: &str = tree
                                .spanned(
                                    ByteSpan::new(refused.end(), half.declaration.span.end())
                                        .ok()?,
                                )?
                                .into();
                            let name = ByteOffset::from(usize::from(refused.end()).saturating_add(
                                rest.len().saturating_sub(rest.trim_start().len()),
                            ));
                            Some((half.declaration.node, name))
                        },
                        Maybe::Present(_) | Maybe::Absent(_) => None,
                    })
            })
            .collect();
        for (declaration, name) in behind {
            let mut at = declaration;
            loop {
                // The lowering never reached this node, so it takes its owner
                // here: a name resolves only where a declaration owns it.
                self.inherit_owner(at);
                let Some((child, node)) = tree.children(at).find_map(|child| {
                    tree.node(child)
                        .filter(|node| node.span().start() <= name && name < node.span().end())
                        .map(|node| (child, node))
                })
                else {
                    break;
                };
                if matches!(node.label(), NodeLabel::Meld(_)) {
                    at = child;
                    continue;
                }
                if node.span().start() == name {
                    self.record_unresolved_run(child, node.span());
                }
                break;
            }
        }
    }

    /// Move each refusal of a declaration of the current source that the
    /// parser repaired to the first bracket the declaration's layout places
    /// elsewhere ([`misplaced()`]), when that bracket comes before it: the
    /// repair follows from the bracket.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: each slot of the current source refused as a malformed form
    ///   the parser repaired, whose declaration — the half whose bytes hold the
    ///   refusal, or the refusing node itself for a slot refused before its
    ///   halves were kept — holds a [`misplaced()`] bracket reported before the
    ///   refusal, is refused there instead, at the same node, naming the form
    ///   of that bracket ([`bracket_form`]) and the bracket's fault; every
    ///   other refusal is unchanged.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the slots.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`]; a definition whose block closes
    ///   twice on one line keeps the doubled closer's refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_doubled_closer_before_a_scope_s_clauses_is_refused_there_5302`
    fn place_by_layout(&mut self)
    {
        let pbg = self.cx().pbg;
        let tree = self.cx().tree;
        let cx = self.cx_mut();
        for slot in cx.collected.slots.iter_mut().skip(cx.current.slots) {
            let Maybe::Present((
                position,
                LoweringRefusal::MalformedForm {
                    span,
                    fault: FormFault::Repaired(_),
                    ..
                },
            )) = slot.refusal
            else {
                continue;
            };
            let holds =
                |within: ByteSpan| within.start() <= span.start() && span.end() <= within.end();
            let half = [slot.signature, slot.definition]
                .into_iter()
                .find_map(|half| match half {
                    Maybe::Present(half) if holds(half.declaration.span) => {
                        Some(half.declaration.span)
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                });
            let own = tree
                .node(position)
                .map(gandr_surface_syntax::Node::span)
                .filter(|&own| holds(own));
            let Some(within) = half.or(own)
            else {
                continue;
            };
            let Maybe::Present(found) = misplaced(pbg, tree, within)
            else {
                continue;
            };
            if found.at.start() < span.start() {
                slot.refusal = Maybe::Present((position, LoweringRefusal::MalformedForm {
                    span: found.at,
                    form: bracket_form(pbg, tree, found.bracket),
                    fault: found.fault,
                }));
            }
        }
    }

    /// Move a refusal of a declaration of the current source onto a word that
    /// misspells a keyword ([`misspelt_keyword`]). The refusal is either an
    /// extra operand after the word, or the word itself as an unknown name
    /// that heads an application ([`applied_word`]). Either way the keyword
    /// read as a name: `retur x`.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: each slot of the current source whose refusal is one of the
    ///   two above, inside a half of the slot, is refused at the word instead
    ///   when [`misspelt_keyword`] reads the word, and, for a word that heads
    ///   an application, when the keyword opens an expression
    ///   ([`opens_expression`]). The refusal keeps its node, names the extra
    ///   operand's form or the declaration's form, and names the keyword the
    ///   word misspells. Every other refusal is unchanged.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the slots.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misspelt_keyword`].
    /// - witness: `gandr-surface-lowering::lower::tests::a_keyword_misspelt_is_refused_at_the_word_2259`
    fn place_misspelt(&mut self)
    {
        let pbg = self.cx().pbg;
        let tree = self.cx().tree;
        let cx = self.cx_mut();
        for slot in cx.collected.slots.iter_mut().skip(cx.current.slots) {
            let Maybe::Present((position, ref refusal)) = slot.refusal
            else {
                continue;
            };
            // An extra operand after a word, or a word that heads an
            // application and names nothing: `retur x` either way.
            let (span, form) = if let LoweringRefusal::MalformedForm {
                span,
                form,
                fault: FormFault::ExtraOperand,
            } = *refusal
            {
                (span, Some(form))
            }
            else if let LoweringRefusal::UnresolvedName { span, .. } = *refusal
                && applied_word(pbg, tree, span).is_some()
            {
                (span, None)
            }
            else {
                continue;
            };
            let Some(half) = [slot.signature, slot.definition]
                .into_iter()
                .find_map(|half| match half {
                    Maybe::Present(half)
                        if half.declaration.span.start() <= span.start()
                            && span.end() <= half.declaration.span.end() =>
                    {
                        Some(half)
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                })
            else {
                continue;
            };
            let within = half.declaration.span;
            // The word's own end, so the search reads the word itself.
            let extra = match form {
                Some(_) => span,
                None => match ByteSpan::new(span.end(), span.end()) {
                    Ok(end) => end,
                    Err(_) => continue,
                },
            };
            // The form the word stands in: the nearest form holding the
            // application, past a block or a statement, which read in their
            // form's place. A function tail is lowered at its declaration, so
            // the declaration of a function names the function's form.
            let holder = |inner: NodeIndex| {
                tree.positions()
                    .find(|&outer| tree.children(outer).any(|child| child == inner))
            };
            let form = if let Some(form) = form {
                form
            }
            else {
                let mut at = applied_word(pbg, tree, span);
                let mut named = None;
                while let Some(outer) = at.and_then(holder) {
                    match tree.node(outer).map(|node| shape_of(pbg, node)) {
                        Some(Ok(Shape::Form { name, .. }))
                            if name != FormName::BLOCK
                                && name != FormName::EXPRESSION_STATEMENT =>
                        {
                            named = Some(
                                if outer == half.declaration.node
                                    && half.operand == Operand::Function
                                {
                                    FormName::FUNCTION
                                }
                                else {
                                    name
                                },
                            );
                            break;
                        },
                        _ => at = Some(outer),
                    }
                }
                let Some(name) = named
                else {
                    continue;
                };
                name
            };
            // A word that heads an application stands where an expression
            // starts, so it misspells only a keyword that opens one there:
            // `here x` is no `where`.
            let applied = matches!(refusal, LoweringRefusal::UnresolvedName { .. });
            if let Some((word, keyword)) = misspelt_keyword(pbg, tree, within, extra)
                && (!applied || opens_expression(pbg, keyword) == KeywordOpening::Expression)
            {
                slot.refusal = Maybe::Present((position, LoweringRefusal::MalformedForm {
                    span: word,
                    form,
                    fault: FormFault::Misspelt(keyword),
                }));
            }
        }
    }

    /// Move a refusal of a declaration of the current source onto a name
    /// that nearly spells an operator tile ([`misspelt_operator`]): `∷∷`, the
    /// cons written twice, read as a name and passed as an operand.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: first, as [`Self::record_runs_behind_repairs`]. Then each
    ///   refused slot of the current source whose half holds such a name at or
    ///   before the start of its refusal is refused at the name instead. A
    ///   zero-width refusal also yields to such a name that starts after it
    ///   with only white space between, and the tile its repair names wins
    ///   among the operators the name is one edit from. The refusal keeps its
    ///   node, names the form of the half that holds the name, and names the
    ///   operator the name misspells. Every other refusal is unchanged.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the slots.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misspelt_operator`], and a repair the parser
    ///   mints just before the name yields to it.
    /// - witness: `gandr-surface-lowering::lower::tests::an_operator_written_twice_is_refused_at_the_run_5301`
    /// - witness: `gandr-surface-lowering::lower::tests::an_operator_near_miss_behind_a_zero_width_repair_is_refused_at_the_run_5512`
    fn place_misspelt_operator(&mut self)
    {
        self.record_runs_behind_repairs();
        let pbg = self.cx().pbg;
        let tree = self.cx().tree;
        let cx = self.cx_mut();
        let unresolved = cx.unresolved.as_slice();
        if unresolved.is_empty() {
            return;
        }
        for slot in cx.collected.slots.iter_mut().skip(cx.current.slots) {
            let Maybe::Present((position, ref refusal)) = slot.refusal
            else {
                continue;
            };
            let Maybe::Present(refused) = refusal.span()
            else {
                continue;
            };
            // The name stands in the half that holds the refusal, at or
            // before the refusal's start: the refused name itself, or an
            // operand before a refusal deeper in the tree. A zero-width
            // refusal is a repair the parser mints, and the name can stand
            // just after it, with only white space between. The tile the
            // repair says the form writes there names the operator.
            let expected = if let LoweringRefusal::MalformedForm {
                fault:
                    FormFault::Repaired(
                        Repair::Diverged(crate::form::Ending::Tile(tile))
                        | Repair::Unended(crate::form::Ending::Tile(tile)),
                    ),
                ..
            } = *refusal
            {
                Some(tile)
            }
            else {
                None
            };
            let found = [slot.signature, slot.definition]
                .into_iter()
                .find_map(|half| match half {
                    Maybe::Present(half)
                        if half.declaration.span.start() <= refused.start()
                            && refused.end() <= half.declaration.span.end() =>
                    {
                        let end = half.declaration.span.end();
                        let reach =
                            ByteSpan::new(half.declaration.span.start(), refused.end()).ok()?;
                        let behind = || {
                            if refused.start() != refused.end() {
                                return None;
                            }
                            let rest: &str = tree
                                .spanned(ByteSpan::new(refused.end(), end).ok()?)?
                                .into();
                            let name = ByteOffset::from(usize::from(refused.end()).saturating_add(
                                rest.len().saturating_sub(rest.trim_start().len()),
                            ));
                            misspelt_operator(
                                pbg,
                                tree,
                                ByteSpan::new(name, end).ok()?,
                                unresolved,
                                expected,
                            )
                            .filter(|&(word, _)| word.start() == name)
                        };
                        misspelt_operator(pbg, tree, reach, unresolved, None)
                            .filter(|&(word, _)| word.start() <= refused.start())
                            .or_else(behind)
                            .map(|found| (half, found))
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                });
            let Some((half, (word, operator))) = found
            else {
                continue;
            };
            let form = if half.operand == Operand::Function {
                FormName::FUNCTION
            }
            else {
                match tree
                    .node(half.declaration.node)
                    .map(|node| shape_of(pbg, node))
                {
                    Some(Ok(Shape::Form { name, .. })) => name,
                    Some(Ok(_) | Err(_)) | None => continue,
                }
            };
            slot.refusal = Maybe::Present((position, LoweringRefusal::MalformedForm {
                span: word,
                form,
                fault: FormFault::MisspeltOperator(operator),
            }));
        }
    }

    /// Move each malformed-form refusal of a declaration of the current
    /// source onto the bare bracket that is open there ([`bare_bracket`]).
    /// The parser reads an element index `xs[i]` as static arguments. The
    /// operand of an index does not always parse as a static argument.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: each slot of the current source refused as a malformed form,
    ///   other than a supply's fault at its own entry, where the half holding
    ///   the refusal, or the line it stands on when no half holds it, holds a
    ///   bare bracket that [`bare_bracket`] finds open at the refusal, is
    ///   refused at that bracket instead, at the same node and naming the same
    ///   form, as a bare index; every other refusal is unchanged.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the slots.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`bare_bracket`], and a misplaced positional
    ///   supply keeps its refusal at its entry.
    /// - witness: `gandr-surface-lowering::lower::tests::a_bare_index_that_parses_as_no_argument_is_refused_at_its_bracket_4944`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_misplaced_positional_supply_is_refused_at_its_entry_4945`
    fn place_bare_index(&mut self)
    {
        let pbg = self.cx().pbg;
        let tree = self.cx().tree;
        let cx = self.cx_mut();
        for slot in cx.collected.slots.iter_mut().skip(cx.current.slots) {
            let Maybe::Present((position, LoweringRefusal::MalformedForm { span, form, fault })) =
                slot.refusal
            else {
                continue;
            };
            // A supply's fault names its entry inside a bracket that holds
            // static arguments, so it stays where it is.
            if matches!(
                fault,
                FormFault::BareIndex
                    | FormFault::PositionalAfterNamed
                    | FormFault::PositionalPastBlock
                    | FormFault::CompoundPositional
                    | FormFault::SuppliedTwice
            ) {
                continue;
            }
            let half = [slot.signature, slot.definition]
                .into_iter()
                .find_map(|half| match half {
                    Maybe::Present(half)
                        if half.declaration.span.start() <= span.start()
                            && span.end() <= half.declaration.span.end() =>
                    {
                        Some(half.declaration.span)
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                });
            // The parser repaired the declaration, so it has no half. The
            // scan reads the line of the refusal.
            let source = tree.source();
            let text: &str = source.as_ref();
            let line = text
                .get(.. usize::from(span.start()))
                .and_then(|before| before.rfind('\n'))
                .map_or(0_usize, |newline| newline.saturating_add(1));
            let Some(within) =
                half.or_else(|| ByteSpan::new(ByteOffset::from(line), span.end()).ok())
            else {
                continue;
            };
            if let Some(bracket) = bare_bracket(pbg, tree, within, span) {
                slot.refusal = Maybe::Present((position, LoweringRefusal::MalformedForm {
                    span: bracket,
                    form,
                    fault: FormFault::BareIndex,
                }));
            }
        }
    }

    /// Keep the uses of every declaration of the current source that the
    /// lowering refused, through [`Self::refused_uses`] over each half it
    /// writes.
    ///
    /// # Specification
    /// - requires: every pass that refuses a declaration of the current source
    ///   has run.
    /// - ensures: [`Self::refused_uses`] over the signature and the definition
    ///   of each refused slot of the current source.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — each walk carries its own predicates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::refused_uses`].
    /// - witness: `gandr-surface-lowering::tests::scopes::a_use_inside_a_refused_form_keeps_its_referent_1265`
    fn refused_declarations(&mut self)
    {
        let halves: Vec<NodeIndex> = self
            .cx()
            .collected
            .slots
            .iter()
            .skip(self.cx().current.slots)
            .filter(|slot| matches!(slot.refusal, Maybe::Present(_)))
            .flat_map(|slot| [slot.signature, slot.definition])
            .filter_map(|half| match half {
                Maybe::Present(half) => Some(half.declaration.node),
                Maybe::Absent(_) => None,
            })
            .collect();
        for declaration in halves {
            self.refused_uses(declaration);
        }
    }

    /// Keep what each name written as a value inside the refused declaration
    /// at `declaration`, and left unread by its refusal, refers to: each such
    /// use resolves under the frame of the innermost form around it that the
    /// lowering read.
    ///
    /// # Specification
    /// - requires: the declaration at `declaration` is refused.
    /// - ensures: each unread name written as an expression under
    ///   `declaration`, whose spelling no unread name written in another
    ///   position inside an unread form under it binds, and that resolves under
    ///   the frame of its innermost read enclosing form, keeps its resolution
    ///   at its span; the readings and the owners are unchanged.
    /// - provides: the uses of a refused declaration for an editor's hover, its
    ///   definitions, references and renames.
    /// - fails: never; a name that does not resolve is passed over.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter and a forked endpoint a `let` names, used
    ///   inside a refused `drop` or `dup`, and a parameter used inside a block
    ///   refused for its joins, each keep their binder.
    /// - witness: `gandr-surface-lowering::tests::scopes::a_use_inside_a_refused_form_keeps_its_referent_1265`
    #[spec(
        captures: before = (usize::from(self.cx().readings.count()), usize::from(self.cx().collected.owner.count())),
        ensures: |_| usize::from(self.cx().readings.count()) == before.0 && usize::from(self.cx().collected.owner.count()) == before.1,
    )]
    fn refused_uses(
        &mut self,
        declaration: NodeIndex,
    )
    {
        // economy: the walk runs only over a refused declaration, so an
        // admitted tree never pays for it.
        let mut forms = alloc::vec![(declaration, Frame::Outermost, false)];
        let mut used: Vec<(Placed, Frame)> = Vec::new();
        let mut bound: BTreeSet<SurfaceName<'source>> = BTreeSet::new();
        while let Some((at, around, enclosed_read)) = forms.pop() {
            let reading = self.cx().reading(at);
            let frame = if reading == Reading::Unread {
                around
            }
            else {
                reading.frame()
            };
            for child in self.cx().tree.children(at) {
                if let Some(NodeLabel::Meld(_) | NodeLabel::Tile(_)) = self
                    .cx()
                    .tree
                    .node(child)
                    .map(gandr_surface_syntax::Node::label)
                {
                    forms.push((child, frame, reading != Reading::Unread));
                }
            }
            let Some(node) = self.cx().tree.node(at)
            else {
                continue;
            };
            let named = matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            );
            if !named || reading != Reading::Unread {
                continue;
            }
            let placed = Placed::of(at, node);
            let expression = match node.label() {
                NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => self
                    .cx()
                    .pbg
                    .mold(mold)
                    .is_ok_and(|def| def.sort == gandr_surface_grammar::Sort::Expression),
                NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc => false,
            };
            if expression {
                used.push((placed, frame));
            }
            // A binder a read form wrote is in that form's frame already, so
            // only one inside an unread form can shadow a use.
            else if !enclosed_read {
                bound.insert(self.cx().name_at(placed));
            }
        }
        for (placed, frame) in used {
            let name = self.cx().name_at(placed);
            if bound.contains(&name) {
                continue;
            }
            let site = Site {
                at: placed,
                name: FormName::DECLARATION,
                reading: Reading::Value(frame),
            };
            if let Ok(Maybe::Present(resolved)) = self.resolve_name(site, frame, name) {
                self.resolved(placed.span, resolved);
            }
        }
    }

    /// The binder frame of a form whose position demands `produced`, with the
    /// bridge the position writes over it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame the position carries when it reads the produced
    ///   sort. An application's head reads a computation and reaches a value by
    ///   a force, and a call or a selection there is nested and forced, which
    ///   the checker runs when it returns a function (#3935, #4818); a
    ///   function's result reads a computation type and reaches a value type by
    ///   a returner; a value position reaches a type of either sort by a quote,
    ///   and a computation as the value it returns at an endpoint or where a
    ///   type reads it, a lambda there as its thunk (#3697, #3767), a lambda
    ///   `cong` maps by as its thunk (#3773), and nested everywhere else; a
    ///   tail, where a path through a body ends, reaches a value by the
    ///   `return` its polarity names, recorded as inferred and leaving; a
    ///   `while` loop's condition, and a tail of a handled subject, which is
    ///   the subject's result, reach a value by a `return` recorded as no exit;
    ///   the bridge is recorded for the form's node, and every other match
    ///   records none.
    /// - provides: the sort check every former takes, and the six insertions
    ///   decided by the sort of a position.
    /// - fails: yields the wrong-sort refusal when the position reads another
    ///   sort no bridge reaches, at the outermost grouping around the form
    ///   ([`Self::standing`](crate::lower::ExpressionsRef::standing)).
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each bridge separated from its bare neighbour: a
    ///   value and a computation at a head, a value type and a computation type
    ///   at a result, a value and a type at a value, a computation at an
    ///   endpoint and elsewhere at a value, a value and a computation at a
    ///   tail, each asserted through the lowered node and its origin's
    ///   provenance.
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `gandr-surface-lowering::lower::loops::tests::a_while_tests_its_condition_on_every_pass`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouped_form_of_the_wrong_sort_is_refused_at_its_parentheses_2341`
    /// - witness: `gandr-surface-lowering::lower::runs::tests::a_call_returning_a_function_runs_where_it_is_applied_3935`
    /// - witness: `gandr-surface-lowering::tests::modules::models::an_operation_selected_off_a_model_binder_calls_in_place_4818`
    #[spec(
        ensures: |ret| {
            let expected = match (site.reading, produced) {
                | (Reading::Head(frame), Produced::Computation)
                    if self.cx().tree.node(site.at.node).is_some_and(|node| matches!(shape_of(self.cx().pbg, node), Ok(Shape::Form { former: Former::Call | Former::Projection, .. }))) =>
                {
                    Some((frame, Bridge::HeadCall))
                },
                | (Reading::Value(frame), Produced::Value)
                | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
                | (Reading::ValueType(frame), Produced::ValueType)
                | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                    Some((frame, Bridge::Bare))
                },
                | (Reading::Head(frame), Produced::Value) => {
                    Some((frame, Bridge::Inserted(Insertion::Force)))
                },
                | (Reading::Result(frame), Produced::ValueType) => {
                    Some((frame, Bridge::Inserted(Insertion::Returner)))
                },
                | (
                    Reading::Value(frame),
                    Produced::ValueType | Produced::CompType,
                ) => Some((frame, Bridge::Inserted(Insertion::Quote))),
                | (Reading::Value(frame), Produced::Computation)
                    if self.cx().over_points.contains_key(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Thunk)))
                },
                | (Reading::Value(frame), Produced::Computation)
                    if self.cx().at_endpoint.contains(&site.at.node) || self.cx().type_read.contains(&site.at.node) =>
                {
                    let lambda = self.cx().tree.node(site.at.node).is_some_and(|node| matches!(shape_of(self.cx().pbg, node), Ok(Shape::Form { former: Former::Lambda, .. })));
                    Some((frame, Bridge::Inserted(if lambda { Insertion::Thunk } else { Insertion::Endpoint })))
                },
                | (Reading::Value(frame), Produced::Computation)
                    if self.cx().let_bound.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Bound)))
                },
                | (Reading::Value(frame), Produced::Computation) => {
                    Some((frame, Bridge::Inserted(Insertion::Nested)))
                },
                | (Reading::Computation(frame), Produced::Value)
                    if self.cx().tested.contains(&site.at.node) || self.cx().results.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Return)))
                },
                | (Reading::Computation(frame), Produced::Value)
                    if self.cx().exits.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Return)))
                },
                | _ => None,
            };
            match expected {
                | Some((frame, bridge)) => {
                    ret == Ok(frame)
                        && self
                            .cx().bridges
                            .get(site.at.node)
                            .is_none_or(|held| *held == bridge)
                        && (bridge != Bridge::Inserted(Insertion::Return)
                            || self.cx().tested.contains(&site.at.node)
                            || self.cx().results.contains(&site.at.node)
                            || (self.cx().inferred.contains(&site.at.node)
                                && self.cx().leaving.contains(&site.at.node)))
                },
                | None => ret == Err(self.shared().standing(site).out(FragmentBoundary::WrongSort)),
            }
        },
    )]
    #[inline]
    pub fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let (frame, bridge) = match (site.reading, produced) {
            // A call or a selection at an application's head may return the
            // function the application reads, which only the checker can say
            // (#3935, #4818).
            (Reading::Head(frame), Produced::Computation)
                if self.cx().tree.node(site.at.node).is_some_and(|node| {
                    matches!(
                        shape_of(self.cx().pbg, node),
                        Ok(Shape::Form {
                            former: Former::Call | Former::Projection,
                            ..
                        })
                    )
                }) =>
            {
                (frame, Bridge::HeadCall)
            },
            (Reading::Value(frame), Produced::Value)
            | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
            | (Reading::ValueType(frame), Produced::ValueType)
            | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                (frame, Bridge::Bare)
            },
            (Reading::Head(frame), Produced::Value) => (frame, Bridge::Inserted(Insertion::Force)),
            (Reading::Result(frame), Produced::ValueType) => {
                (frame, Bridge::Inserted(Insertion::Returner))
            },
            (Reading::Value(frame), Produced::ValueType | Produced::CompType) => {
                (frame, Bridge::Inserted(Insertion::Quote))
            },
            // A lambda `cong` maps by is minted as its thunk, whose body the
            // transport's motive reads (#3773).
            (Reading::Value(frame), Produced::Computation)
                if self.cx().over_points.contains_key(&site.at.node) =>
            {
                (frame, Bridge::Inserted(Insertion::Thunk))
            },
            (Reading::Value(frame), Produced::Computation)
                if self.cx().at_endpoint.contains(&site.at.node)
                    || self.cx().type_read.contains(&site.at.node) =>
            {
                // A lambda there is checked at a thunk type, an endpoint's
                // carrier or a parameter's, and a type elaborates no nested
                // computation, so it is its thunk (#3697, #3767).
                let lambda = self.cx().tree.node(site.at.node).is_some_and(|node| {
                    matches!(
                        shape_of(self.cx().pbg, node),
                        Ok(Shape::Form {
                            former: Former::Lambda,
                            ..
                        })
                    )
                });
                let insertion = if lambda {
                    Insertion::Thunk
                }
                else {
                    Insertion::Endpoint
                };
                (frame, Bridge::Inserted(insertion))
            },
            (Reading::Value(frame), Produced::Computation)
                if self.cx().let_bound.contains(&site.at.node) =>
            {
                (frame, Bridge::Inserted(Insertion::Bound))
            },
            (Reading::Value(frame), Produced::Computation) => {
                (frame, Bridge::Inserted(Insertion::Nested))
            },
            (Reading::Computation(frame), Produced::Value)
                if self.cx().tested.contains(&site.at.node)
                    || self.cx().results.contains(&site.at.node) =>
            {
                (frame, Bridge::Inserted(Insertion::Return))
            },
            (Reading::Computation(frame), Produced::Value)
                if self.cx().exits.contains(&site.at.node) =>
            {
                let _tail = self.cx_mut().inferred.insert(site.at.node);
                let _exit = self.cx_mut().leaving.insert(site.at.node);
                (frame, Bridge::Inserted(Insertion::Return))
            },
            _ => {
                return Err(self
                    .shared()
                    .standing(site)
                    .out(FragmentBoundary::WrongSort));
            },
        };
        if let Some(held) = self.cx_mut().bridges.get_mut(site.at.node) {
            *held = bridge;
        }
        // A type a term quotes, where no type reads it, is a body's: its reads
        // count in its own telescope (#547).
        if bridge == Bridge::Inserted(Insertion::Quote)
            && !self.cx().type_read.contains(&site.at.node)
            && !self.cx().in_type.contains(&site.at.node)
        {
            let cx = self.cx_mut();
            let _quote = cx.in_quote.insert(site.at.node);
            cx.in_quote.extend(cx.tree.children(site.at.node));
        }

        Ok(frame)
    }

    /// What `name`, written at `site` under `frame`, resolves to: the
    /// innermost binder carrying it, else a declaration strictly earlier than
    /// the one `site` belongs to, another member of its mutual block, or that
    /// declaration itself when it is a data declaration, searched from that
    /// declaration's own module outward to the top level.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node.
    /// - ensures: the binder with its index and its written type; else the
    ///   member a module a block opens over `site` exports under the name
    ///   ([`Self::opened_name`]); else, in a flow's body, the component of the
    ///   flow's domain of that name, whose slot precedes the body's, untyped,
    ///   the body's own members never read; else the first module, innermost
    ///   first, whose body declares the name: its member when that member's
    ///   admission position is strictly earlier, and the forward-member refusal
    ///   when it is not; else a top-level declaration strictly earlier or
    ///   another member of the mutual block `site` belongs to, with its
    ///   admission position and its signature's written type; the data
    ///   declaration `site` belongs to, untyped, for its own name: a family's
    ///   self reference, whose positivity the checker judges; else a callable
    ///   operation admitted strictly earlier, untyped; else what the source's
    ///   imports answer; else, for `Theory`, the presentation code admitted
    ///   strictly earlier, untyped, when the source or one it imports holds a
    ///   `theory` block ([`Collected::theory_in`]); the unresolved absence when
    ///   nothing answers.
    /// - provides: the one resolution term names, capitalised names and type
    ///   heads share.
    /// - fails: [`LoweringRefusal::UnmarkedSelfReference`] for the name a
    ///   recursive function's fixpoint binds, which only a descent claim reads;
    ///   [`LoweringRefusal::ForwardMemberReference`] for a member of an
    ///   enclosing module declared at or after the referring declaration;
    ///   [`LoweringRefusal::ImportShadows`] where a module a block opens and
    ///   another scope answer the name distinctly ([`Self::opened_name`]);
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnmarkedSelfReference`],
    /// [`LoweringRefusal::ForwardMemberReference`],
    /// [`LoweringRefusal::ImportShadows`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member named by an earlier sibling, by a later one,
    ///   by itself, from a nested module and from the top level, each asserted
    ///   as the exact constant or refusal.
    /// - witness: `gandr-surface-lowering::tests::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_self_reference_is_unresolved`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_family_names_itself_in_its_fields`
    /// - witness: `gandr-surface-lowering::lower::tests::an_earlier_declaration_resolves_as_a_constant`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_unmarked_self_reference_is_refused_with_its_claim`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_import_via_a_flow_reads_its_source_through_it_3378`
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: |ret| {
            self.cx().fuel.remaining() <= before
                && match ret {
                    | Ok(Maybe::Present(Resolved::Declaration { constant, declared })) => {
                        matches!(self.cx().collected.owner_of(site.at.node), Maybe::Present(own) if self.cx().collected.slots.get(usize::from(constant)).is_some_and(|entry| entry.constant == constant && ((entry.name == name && (usize::from(constant) < usize::from(own) || (usize::from(constant) == usize::from(own) && matches!(entry.definition, Maybe::Present(Half { operand: Operand::Data(_), .. }))) || matches!((self.cx().collected.block_of(SlotIndex::from(usize::from(constant))), self.cx().collected.block_of(own)), (Maybe::Present(held), Maybe::Present(holding)) if held == holding)) && declared == match entry.signature { Maybe::Present(Half { operand: Operand::Written(written), .. }) => Maybe::Present(written.node), Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped) }) || matches!(self.cx().collected.imported_slot(self.cx().collected.unit.source_at(site.at.span.start()), name), Ok(Maybe::Present((slot, _))) if usize::from(slot) == usize::from(constant)))))
                    },
                    | Err(
                        LoweringRefusal::ForwardMemberReference {
                            span,
                            name: refused,
                            ..
                        }
                        | LoweringRefusal::UnmarkedSelfReference {
                            span,
                            name: refused,
                        },
                    ) => span == site.at.span && refused == name,
                    | _ => true,
                }
        },
    )]
    #[inline]
    pub fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let cx = self.cx_mut();
        if let Maybe::Present(bound) = cx.scope.resolve(frame, name, &mut cx.fuel)? {
            if self.cx().recursions.contains_key(&bound.binder) {
                return Err(LoweringRefusal::UnmarkedSelfReference {
                    span: site.at.span,
                    name,
                });
            }
            return Ok(Maybe::Present(Resolved::Binder(bound)));
        }
        let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        self.past_binders(site, own, name)
    }

    /// What the modules a block opens over `site` and the declarations
    /// enclosing it, owned by the declaration `own`, answer `name` with:
    /// [`Self::resolve_name`] past the binders.
    ///
    /// # Specification
    /// - requires: `own` owns `site`.
    /// - ensures: the member a module open over `site` exports under the name
    ///   ([`Self::opened_name`]); else what [`Self::declared_name`] answers.
    /// - provides: the one order a use and a binder read past the binders.
    /// - fails: as [`Self::opened_name`] and [`Self::declared_name`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`],
    /// [`LoweringRefusal::ImportShadows`],
    /// [`LoweringRefusal::UnexportedName`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resolve_name`].
    /// - witness: `gandr-surface-lowering::lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: |_| self.cx().fuel.remaining() <= before,
    )]
    fn past_binders(
        &mut self,
        site: Site,
        own: SlotIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        if !self.cx().opened.is_empty()
            && let opened @ Maybe::Present(_) = self.opened_name(site, own, name)?
        {
            return Ok(opened);
        }
        self.declared_name(site, own, name)
    }

    /// The binding a binder spelling `name`, written at `binder` and
    /// extending `frame`, hides: what a use of the name written there would
    /// read. `root` is where the outermost scope declares the name.
    ///
    /// # Specification
    /// - requires: `frame` is the frame the binder extends, and `root` is
    ///   [`Recognition::site`](gandr_surface_lowering_base::namespace::Recognition::site)
    ///   of the name's one-segment path.
    /// - ensures: the written site of the innermost binder of the chain rooted
    ///   at `frame` that carries `name`; else the declaration
    ///   [`Self::past_binders`] answers; else the builtin, when `root` is one.
    ///   Absent when that binder is unwritten, when the lookup past the binders
    ///   refuses the name, and when nothing answers it. The reached imports are
    ///   as they were.
    /// - provides: the hidden binding [`Self::note_binder`] keeps.
    /// - fails: propagates [`LoweringRefusal::BudgetExceeded`] from the lookup,
    ///   which spends fuel as a use's does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern binder over a parameter, a parameter over
    ///   an earlier declaration, an opened member and an import, a binder over
    ///   a builtin, over a later declaration and over a name two imports bind,
    ///   each asserted as the exact event or its absence, and the reached
    ///   imports unchanged.
    /// - witness: `gandr-surface-lowering::tests::scopes::each_shadowing_binder_keeps_the_binding_it_hides_6270`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_shadowing_binder_hides_an_import_and_reaches_none_6270`
    /// - witness: `gandr-surface-lowering::tests::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
    #[spec(
        captures: before = (self.cx().fuel.remaining(), self.cx().collected.reached.len()),
        ensures: |ret| self.cx().fuel.remaining() <= before.0
            && self.cx().collected.reached.len() == before.1
            && ret.as_ref().err().is_none_or(|refusal| matches!(refusal, LoweringRefusal::BudgetExceeded { .. })),
    )]
    fn hidden_by(
        &mut self,
        binder: Placed,
        frame: Frame,
        name: SurfaceName<'source>,
        root: Maybe<RecognitionSite, crate::namespace::binding::Absent>,
    ) -> Result<Maybe<crate::Resolution, hidden::Absent>, LoweringRefusal<'source>>
    {
        let cx = self.cx_mut();
        if let Maybe::Present(bound) = cx.scope.resolve(frame, name, &mut cx.fuel)? {
            return Ok(match self.cx().scope.site(bound.binder) {
                Maybe::Present(site) => Maybe::Present(crate::Resolution::Binder(site)),
                Maybe::Absent(_) => Maybe::Absent(hidden::Absent::Unwritten),
            });
        }
        if let Maybe::Present(own) = self.cx().collected.owner_of(binder.node) {
            let site = Site {
                at: binder,
                name: FormName::IDENTIFIER,
                reading: Reading::Unread,
            };
            // A use reaches the import it reads through, and a binder reads
            // none: the lookup reaches into a set that is then dropped.
            let reached = core::mem::take(&mut self.cx_mut().collected.reached);
            let found = self.past_binders(site, own, name);
            self.cx_mut().collected.reached = reached;
            match found {
                Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => {
                    return Ok(Maybe::Present(crate::Resolution::Declaration(constant)));
                },
                Ok(Maybe::Present(Resolved::Binder(_)) | Maybe::Absent(_)) => {},
                Err(refusal @ LoweringRefusal::BudgetExceeded { .. }) => return Err(refusal),
                Err(_) => return Ok(Maybe::Absent(hidden::Absent::Refused)),
            }
        }
        Ok(match root {
            Maybe::Present(RecognitionSite::Builtin) => Maybe::Present(crate::Resolution::Builtin),
            Maybe::Present(RecognitionSite::Source(_)) | Maybe::Absent(_) => {
                Maybe::Absent(hidden::Absent::Unbound)
            },
        })
    }

    /// What the declarations enclosing `site`, owned by the declaration `own`,
    /// answer `name` with: [`Self::resolve_name`] past the binders and the
    /// modules a block opens.
    ///
    /// # Specification
    /// - requires: `own` owns `site`.
    /// - ensures: as [`Self::resolve_name`], from the flow's domain on.
    /// - provides: the declaration half of [`Self::resolve_name`], which an
    ///   opened module's answer is weighed against.
    /// - fails: as [`Self::resolve_name`], but for the self-reference refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resolve_name`].
    /// - witness: `gandr-surface-lowering::tests::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `gandr-surface-lowering::lower::opening::tests::a_name_two_scopes_answer_is_refused_at_its_use`
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: |_| self.cx().fuel.remaining() <= before,
    )]
    fn declared_name(
        &mut self,
        site: Site,
        own: SlotIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let mut container = self.cx().collected.slots.get(usize::from(own)).map_or_else(
            || self.cx().collected.top(site.at.span.start()),
            |slot| slot.container,
        );
        loop {
            self.cx_mut().fuel.spend()?;
            // A flow's body reads its domain's members by name and never its
            // own, so `def answer = answer ;` reads the domain's `answer`.
            if let Maybe::Present((parameter, outer)) = self.shared().domain_scope(container) {
                if let Some(slot) = self.shared().parameter_export(parameter, name)
                    && let Some(entry) = self.cx().collected.slots.get(usize::from(slot))
                {
                    let declared = match entry.signature {
                        Maybe::Present(Half {
                            operand: Operand::Written(written),
                            ..
                        }) => Maybe::Present(written.node),
                        Maybe::Present(_) | Maybe::Absent(_) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    };
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared,
                    }));
                }
                container = outer;
                continue;
            }
            if let Some(&target) = self.cx().collected.by_name.get(&(container, name))
                && let Some(entry) = self.cx().collected.slots.get(usize::from(target))
            {
                let own_family = target == own
                    && matches!(
                        entry.definition,
                        Maybe::Present(Half {
                            operand: Operand::Data(_),
                            ..
                        })
                    );
                // A mutual block's members name one another in any order:
                // the block is admitted as one. A member's own name is the
                // rule above's.
                let one_block = target != own
                    && matches!(
                        (self.cx().collected.block_of(target), self.cx().collected.block_of(own)),
                        (Maybe::Present(held), Maybe::Present(holding)) if held == holding
                    );
                if target < own || own_family || one_block {
                    let declared = match entry.signature {
                        Maybe::Present(Half {
                            operand: Operand::Written(written),
                            ..
                        }) => Maybe::Present(written.node),
                        Maybe::Present(_) | Maybe::Absent(_) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    };
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared,
                    }));
                }
                if let Container::Module(_) = container {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name,
                        declared: entry.named.span,
                    });
                }
            }
            let Container::Module(module) = container
            else {
                let source = self.cx().collected.unit.source_at(site.at.span.start());
                if let Some(&target) = self.cx().collected.operation_names.get(&(source, name))
                    && target < own
                    && let Some(entry) = self.cx().collected.slots.get(usize::from(target))
                {
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared: Maybe::Absent(binder_type::Absent::Untyped),
                    }));
                }
                let imported = self.imported(site, source, name)?;
                if let Maybe::Absent(_) = imported
                    && name.as_ref() == THEORY_CODE
                    && let Maybe::Present(code) = self.cx().collected.theory_in(source)
                    && code < own
                    && let Some(constant) = self
                        .cx()
                        .collected
                        .slots
                        .get(usize::from(code))
                        .map(|entry| entry.constant)
                {
                    if let Some(import) = self.cx().collected.theory_import(source) {
                        self.cx_mut().collected.reach(import);
                    }
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant,
                        declared: Maybe::Absent(binder_type::Absent::Untyped),
                    }));
                }
                return Ok(imported);
            };
            container = self
                .cx()
                .collected
                .structures
                .get(usize::from(module))
                .map_or_else(
                    || self.cx().collected.top(site.at.span.start()),
                    |structure| structure.container,
                );
        }
    }

    /// What the sources `source` imports unqualified answer `name`, used at
    /// `site`, with.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node, in `source`.
    /// - ensures: the constant and written signature type of the top-level
    ///   declaration one imported source declares under `name`, or the
    ///   unresolved absence when none does.
    /// - provides: the import fallback of [`Self::resolve_name`].
    /// - fails: [`LoweringRefusal::ImportShadows`] when two imports declare the
    ///   name, naming both; [`LoweringRefusal::UnexportedName`] when the
    ///   declaration has a signature and no definition, or when no imported
    ///   source exports it and one keeps it private, which its source does not
    ///   export.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ImportShadows`] and
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name one import answers, a name two answer, a
    ///   pending declaration and a private one, each asserted exactly.
    /// - witness: `gandr-surface-lowering::tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
    /// - witness: `gandr-surface-lowering::tests::namespace::two_imports_binding_one_name_refuse_its_use`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_pending_declaration_is_not_exported`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_private_declaration_is_refused_to_its_importer_2687`
    #[spec(ensures: |ref ret| match *ret {
        Ok(_) => true,
        Err(LoweringRefusal::ImportShadows { name: found, .. } | LoweringRefusal::UnexportedName { name: found, .. }) => {
            found.as_ref() == name.as_ref()
        },
        Err(_) => false,
    })]
    fn imported(
        &mut self,
        site: Site,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let (target, import) = match self.cx().collected.imported_slot(source, name) {
            Ok(Maybe::Present(found)) => found,
            Ok(Maybe::Absent(_)) => {
                let Maybe::Present((private, import)) =
                    self.cx().collected.private_slot(source, name)
                else {
                    return Ok(Maybe::Absent(named::Absent::Unresolved));
                };
                self.cx_mut().collected.reach(import);
                return Err(self.shared().private(site, name, private));
            },
            Err(ambiguity) => {
                return Err(LoweringRefusal::ImportShadows {
                    span: site.at.span,
                    name,
                    import: ambiguity.import,
                    other: ambiguity.other,
                });
            },
        };
        self.cx_mut().collected.reach(import);
        self.shared().exported(site, name, target)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The declaration at `target`, which another source exports under
    /// `name`, read at `site`.
    ///
    /// # Specification
    /// - requires: `target` is a top-level declaration of a source the site's
    ///   source imports, or the image of a flow's member an import of it binds.
    /// - ensures: its constant and written signature type; for an image, its
    ///   constant and no written type, whatever its visibility, since it is the
    ///   importer's own; the unresolved absence for a slot the collection does
    ///   not hold.
    /// - fails: [`LoweringRefusal::UnexportedName`] for a declaration its
    ///   source keeps private, and for one with a signature and no definition.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses of
    ///   [`Self::imported`](crate::lower::Expressions::imported).
    /// - witness: `gandr-surface-lowering::tests::namespace::a_pending_declaration_is_not_exported`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_private_declaration_is_refused_to_its_importer_2687`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_import_via_a_flow_reads_its_source_through_it_3378`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => self
            .cx().collected
            .slots
            .get(usize::from(target))
            .is_some_and(|entry| entry.constant == constant),
        Ok(Maybe::Absent(_)) => self.cx().collected.slots.get(usize::from(target)).is_none(),
        Err(LoweringRefusal::UnexportedName { name: found, .. }) => found.as_ref() == name.as_ref(),
        Ok(Maybe::Present(_)) | Err(_) => false,
    })]
    fn exported(
        &self,
        site: Site,
        name: SurfaceName<'source>,
        target: SlotIndex,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let Some(entry) = self.cx().collected.slots.get(usize::from(target))
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        if self.cx().collected.translates(target).0 {
            return Ok(Maybe::Present(Resolved::Declaration {
                constant: entry.constant,
                declared: Maybe::Absent(binder_type::Absent::Untyped),
            }));
        }
        if self.cx().collected.slot_visibility(target) == Visibility::Private {
            return Err(self.private(site, name, target));
        }
        if let Maybe::Absent(_) = entry.definition {
            return Err(LoweringRefusal::UnexportedName {
                span: site.at.span,
                name,
                declared: entry.named.span,
                reason: Unexported::Undefined,
            });
        }
        let declared = match entry.signature {
            Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) => Maybe::Present(written.node),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
        };

        Ok(Maybe::Present(Resolved::Declaration {
            constant: entry.constant,
            declared,
        }))
    }

    /// The refusal of `name`, read at `site`, which another source declares
    /// at `target` and keeps private.
    ///
    /// # Specification
    /// trivial.
    fn private(
        &self,
        site: Site,
        name: SurfaceName<'source>,
        target: SlotIndex,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::UnexportedName {
            span: site.at.span,
            name,
            declared: self
                .cx()
                .collected
                .slots
                .get(usize::from(target))
                .map_or(site.at.span, |entry| entry.named.span),
            reason: Unexported::Private,
        }
    }

    /// Refuse the member `target` of the module `module`, read at `site`,
    /// when another source declares it and keeps the module private.
    ///
    /// # Specification
    /// - requires: `target` is the slot the module path at `site` resolves to,
    ///   and `module` the path's head.
    /// - ensures: nothing when the site's source declares `target`, or when its
    ///   source exports it.
    /// - fails: [`LoweringRefusal::UnexportedName`], naming `module`, for a
    ///   member of a module another source keeps private.
    /// - panics: none.
    /// - executable: none — the clause would restate the comparison of the two
    ///   sources and the slot's visibility whole.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member of a private module read beside it and from
    ///   an importer, and a member of an exported one.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_private_declaration_is_refused_to_its_importer_2687`
    /// - witness: `gandr-surface-lowering::tests::namespace::each_import_a_name_is_read_through_is_reached`
    fn exported_across(
        &self,
        site: Site,
        module: SurfaceName<'source>,
        target: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let unit = &self.cx().collected.unit;
        let declared = self
            .cx()
            .collected
            .slots
            .get(usize::from(target))
            .map(|entry| unit.source_at(entry.introduced_by.span.start()));
        if declared.is_some_and(|source| source != unit.source_at(site.at.span.start()))
            && self.cx().collected.slot_visibility(target) == Visibility::Private
        {
            return Err(self.private(site, module, target));
        }
        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// What `alias.selected`, written at `site`, names when `alias` is the
    /// alias of a path import of the site's source, or the module path a
    /// qualified import binds, `text.greet` of `text.greet.greeting`.
    ///
    /// # Specification
    /// - requires: `alias` is the head of the path at `site`, a name or a path
    ///   of names, and `selected` its selected name.
    /// - ensures: the top-level declaration the imported source declares under
    ///   the selected name, or, for an import read through a flow, the member
    ///   its translation binds; the unaliased absence when `alias`, as written,
    ///   is no alias or module path of the source or names an import of an
    ///   address no source of the unit answers. A constructor is not selected
    ///   through an alias: a selected name is lowercase, so a qualified
    ///   constructor does not parse.
    /// - provides: the qualified reading of an aliased or qualified import.
    /// - fails: [`LoweringRefusal::UnknownMember`] for a name the imported
    ///   source does not declare, or that the signature the import is written
    ///   at does not state; [`LoweringRefusal::UnexportedName`] for one it
    ///   keeps private or declares without a definition;
    ///   [`LoweringRefusal::UnlockedDependency`] at the alias for any name read
    ///   through an import resolved to [`ImportTarget::Unlocked`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMember`], [`LoweringRefusal::UnexportedName`]
    /// and [`LoweringRefusal::UnlockedDependency`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an aliased family and value each read from the
    ///   imported source, an undeclared member refused by name, a pending
    ///   member refused at the member, and a name read through an unlocked
    ///   alias refused at the alias while its source's other declarations
    ///   stand; a member the source exports beyond the import's signature
    ///   refused by name.
    /// - witness: `gandr-surface-lowering::tests::namespace::an_aliased_import_qualifies_its_source_s_names`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_pending_member_read_through_an_alias_is_refused_at_the_member`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_name_read_through_an_unlocked_alias_is_refused_at_it_3072`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_import_at_a_narrower_signature_settles_3098`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_import_via_a_flow_reads_its_source_through_it_3378`
    #[spec(ensures: |ref ret| matches!(
        *ret,
        Ok(_) | Err(LoweringRefusal::UnknownMember { .. } | LoweringRefusal::UnexportedName { .. }
            | LoweringRefusal::UnlockedDependency { .. })
    ))]
    fn aliased_member(
        &mut self,
        site: Site,
        alias: Placed,
        selected: Placed,
    ) -> Result<Maybe<Resolved, alias_member::Absent>, LoweringRefusal<'source>>
    {
        let source = self.cx().collected.unit.source_at(site.at.span.start());
        let module = self
            .cx()
            .tree
            .spanned(alias.span)
            .map_or_else(|| self.cx().name_at(alias), SurfaceName::from);
        let cx = self.cx_mut();
        let Maybe::Present(import) = cx.collected.imports.aliased(source, module)
        else {
            return Ok(Maybe::Absent(alias_member::Absent::Unaliased));
        };
        let target = match import.resolution() {
            ImportResolution::Path(ImportTarget::Source(target)) => target,
            ImportResolution::Path(ImportTarget::Unlocked) => {
                return Err(LoweringRefusal::UnlockedDependency {
                    span: alias.span,
                    alias: module,
                });
            },
            ImportResolution::Path(ImportTarget::Unresolved | ImportTarget::Cycle)
            | ImportResolution::Foreign => {
                return Ok(Maybe::Absent(alias_member::Absent::Unaliased));
            },
        };
        let member = cx.name_at(selected);
        let unknown = LoweringRefusal::UnknownMember {
            span: selected.span,
            module,
            member,
        };
        if !import.states(member).0 {
            return Err(unknown);
        }
        let found = match *import.signature() {
            Maybe::Present(ImportSignature {
                via: Maybe::Present(ref translation),
                ..
            }) => match cx.collected.translated(translation, member) {
                Maybe::Present(slot) => Some(slot),
                Maybe::Absent(_) => None,
            },
            Maybe::Present(ImportSignature { ref renaming, .. }) => cx
                .collected
                .by_name
                .get(&(Container::TopLevel(target), *renaming.read(&member)))
                .copied(),
            Maybe::Absent(_) => cx
                .collected
                .by_name
                .get(&(Container::TopLevel(target), member))
                .copied(),
        };
        let Some(slot) = found
        else {
            return Err(unknown);
        };
        cx.collected.reach(import.span());
        let read = Site {
            at: selected,
            ..site
        };
        match self.shared().exported(read, member, slot)? {
            Maybe::Present(resolved) => Ok(Maybe::Present(resolved)),
            Maybe::Absent(_) => Err(unknown),
        }
    }

    /// Classify a term name.
    ///
    /// # Specification
    /// - requires: `site` is an identifier in term position.
    /// - ensures: a name standing as a value resolves against the binder frame
    ///   first and the declarations strictly earlier than its own second, and
    ///   is planned as the variable or constant it resolved to; a binder named
    ///   inside a type is planned as [`Self::resolved_term`] plans it; a name
    ///   nothing binds that spells a type atom, as `f64` does, stands as that
    ///   type, quoted, as a capitalised atom such as `Integer` does.
    /// - provides: the term-name half of resolution.
    /// - fails: yields the wrong-sort refusal for a name in computation
    ///   position, [`LoweringRefusal::RegionAsValue`] for a region binder of
    ///   the definition the name stands in that nothing nearer binds,
    ///   [`LoweringRefusal::ModelImplicitValue`] for a model implicit named
    ///   alone and [`LoweringRefusal::InertRead`] for an inert component read
    ///   from content, as [`Self::resolved_term`] refuses each, and the
    ///   unresolved-name refusal when no scope answers; propagates
    ///   [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — local binders and earlier declarations resolve to
    ///   their own variable or constant, while an undefined name keeps its
    ///   source span.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `gandr-surface-lowering::lower::tests::an_undefined_term_name_is_refused`
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `gandr-surface-lowering::lower::tests::a_number_takes_float64_from_its_suffix_or_annotation_1830`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Variable(..) | Plan::Constant(_) | Plan::Primitive(_) | Plan::StaticApplication(..) | Plan::ListNil | Plan::Atom(_)))
                )
        },
    )]
    fn name(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let name = self.cx().name_at(site.at);
        match self.resolve_name(site, frame, name)? {
            Maybe::Present(resolved) => {
                self.resolved(site.at.span, resolved);
                let plan = self.resolved_term(site, frame, resolved)?;
                self.plan(site, plan);
                ModelsRef::new(self.host_ref()).opened_model(site)
            },
            Maybe::Absent(_) => {
                if name.as_ref() == identity::NIL {
                    self.plan(site, Plan::ListNil);
                    return Ok(());
                }
                if let Maybe::Present(atom) = self.shared().atom(name) {
                    let _frame = self.require(site, Produced::ValueType)?;
                    self.plan(site, Plan::Atom(atom));
                    return Ok(());
                }
                let path = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
                if let PathResolution::Complete(Recognized::BuiltinPrimitive {
                    primitive, ..
                }) = self.cx().recognition.resolve_path(&path)
                {
                    self.plan(site, Plan::Primitive(primitive));
                    Ok(())
                }
                else if self.shared().region_binder(site.at.node, name).is_some() {
                    Err(LoweringRefusal::RegionAsValue {
                        span: site.at.span,
                        name,
                    })
                }
                else {
                    Err(LoweringRefusal::UnresolvedName {
                        span: site.at.span,
                        name,
                    })
                }
            },
        }
    }

    /// Plan the label tile `label` of a punned entry, `.l` in a record or in
    /// an instantiation slot, as the name `l` it spells, read as a value under
    /// `frame`. The tile is a piece of its entry's form, so the sweep never
    /// classifies it as a form of its own.
    ///
    /// # Specification
    /// - requires: `label` is an entry's label tile.
    /// - ensures: as [`Self::name`] at the tile; the tile is kept out of the
    ///   classifying sweep.
    /// - fails: as [`Self::name`].
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a punned record field and a punned implicit supply
    ///   each lower to the variable they name, and a pun naming nothing is
    ///   refused as unresolved.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_telescope_value_lowers_by_its_arity`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::supply_by_name_is_order_free`
    #[spec(ensures: |ret| ret.is_err() || self.cx().classified_ahead.contains(&label.node))]
    #[inline]
    pub fn pun(
        &mut self,
        label: Placed,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _first = self.cx_mut().classified_ahead.insert(label.node);
        self.name(Site {
            at: label,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        })
    }

    /// Classify a capitalised name in term position.
    ///
    /// # Specification
    /// - requires: `site` is a constructor in term position.
    /// - ensures: a constructor of a data family declared strictly earlier
    ///   stands as that constructor applied to no fields; otherwise a data
    ///   family an earlier declaration answers stands as its type, which a
    ///   value position quotes, and any other name a binder or an earlier
    ///   declaration answers stands as the value it resolved to; otherwise a
    ///   type component or type member the name states, read as
    ///   [`Self::stated_type`] reads it, or a type atom, or `Type` for the
    ///   value universe at the fuss-free level, stands as a type, which a value
    ///   position quotes; otherwise a module declared before it stands as its
    ///   model, as `Models::module_value` packs it.
    /// - provides: the term-position spelling of a type, of a nullary
    ///   constructor, and of a declaration named with a capital.
    /// - fails: yields the wrong-sort refusal for a resolved name or a type
    ///   where its position reads neither; a constructor's own refusals; the
    ///   arity refusal for a family of parameters named alone; a module's
    ///   packing refusal; a name nothing answers is unresolved.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration, a type atom, the universe and an
    ///   unanswered constructor each written where a value is read, asserted as
    ///   the exact core node or refusal; an unknown constructor unresolved.
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::tests::u_and_f_are_names`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_family_named_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::an_unknown_capital_where_a_value_is_read_is_unresolved_2653`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_module_named_where_a_value_is_read_is_its_model_4485`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(
                        &(Plan::Variable(..)
                            | Plan::StaticApplication(..)
                            | Plan::Constant(_)
                            | Plan::Atom(_)
                            | Plan::Universe(_)
                            | Plan::Constructor(_)
                            | Plan::Data(..)
                            | Plan::Codata(..)
                            | Plan::Transparent(_)
                            | Plan::Sealed(_)
                            | Plan::Instantiated(..)
                            | Plan::Packed(_))
                    )
                )
        },
    )]
    fn constructor(
        &mut self,
        site: Site,
        mut cursor: Option<Cursor<'_>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.cx().name_at(site.at);
        if let Maybe::Present(constructor) =
            Native::new(self.host()).named_constructor(site, name)?
        {
            self.constructed_at(site.at.span, constructor);
            let none = Stretch {
                start: self.cx().operands.entries().len(),
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).construct(site, constructor, none);
        }
        if let Maybe::Present(resolved) = self.resolve_name(site, site.reading.frame(), name)? {
            self.resolved(site.at.span, resolved);
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = NativeRef::over(self.cx()).data_family(constant)
            {
                let none = Stretch {
                    start: self.cx().operands.entries().len(),
                    end: self.cx().operands.entries().len(),
                };
                return Native::new(self.host()).family(site, constant, arity, none);
            }
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = NativeRef::over(self.cx()).codata_family(constant)
            {
                let none = Stretch {
                    start: self.cx().operands.entries().len(),
                    end: self.cx().operands.entries().len(),
                };
                return Native::new(self.host()).codata_type(site, constant, arity, none);
            }
            let frame = self.require(site, Produced::Value)?;
            let plan = self.resolved_term(site, frame, resolved)?;
            self.plan(site, plan);
            return Ok(());
        }
        if let Maybe::Present(stated) = self.stated_named(site, name)? {
            return self.stated_type(site, stated);
        }
        let quoted = match self.shared().atom(name) {
            Maybe::Present(atom) => Plan::Atom(atom),
            Maybe::Absent(_) if name.as_ref() == TileName::UNIVERSE.as_ref() => {
                Plan::Universe(match cursor.as_mut() {
                    Some(cursor) => self.shared().universe_of(site, cursor)?,
                    None => Universe::FUSS_FREE,
                })
            },
            Maybe::Absent(_) => {
                if Models::new(self.host()).module_value(site, name)? == Maybe::Present(()) {
                    return Ok(());
                }
                return Err(LoweringRefusal::UnresolvedName {
                    span: site.at.span,
                    name,
                });
            },
        };
        let _frame = self.require(site, Produced::ValueType)?;
        self.plan(site, quoted);

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Admit the read, at `site`, of the declaration at `reached`: the phase
    /// rule, then the inert rule.
    ///
    /// # Specification
    /// - requires: `site` is a name or a path read as a value, and `reached` is
    ///   the declaration's slot it resolved to.
    /// - ensures: nothing when both rules admit the read.
    /// - provides: the one admission every read of a declaration's slot passes;
    ///   no read site runs either rule alone.
    /// - fails: [`LoweringRefusal::PhaseDependence`] where [`Self::phased`]
    ///   refuses the read; else [`LoweringRefusal::InertRead`] where
    ///   [`Self::inert_read`] does.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::phased`] and [`Self::inert_read`].
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_reads_types_and_never_values`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_type_member_never_reads_its_parameter_s_value`
    /// - witness: `gandr-surface-lowering::tests::modules::models::an_inert_field_is_read_only_by_another_3029`
    #[spec(ensures: |ret| matches!(ret, Ok(()) | Err(LoweringRefusal::PhaseDependence { .. } | LoweringRefusal::InertRead { .. })))]
    fn admit_read(
        &self,
        site: Site,
        reached: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.phased(site, reached)?;
        self.inert_read(site, inert::Read::Slot(reached))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The plan a name that resolved to `resolved` stands as, read as a value
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - requires: `resolved` is what the name at `site` resolves to.
    /// - ensures: a binder named inside a type is mentioned, so the arrow that
    ///   binds it is dependent, and planned as the bare code it names, minted
    ///   at its telescope index; any other resolution is the variable or the
    ///   constant it names.
    /// - provides: the one place a term name inside a type reads the type's
    ///   telescope rather than the term context.
    /// - fails: [`LoweringRefusal::PhaseDependence`] and
    ///   [`LoweringRefusal::InertRead`] where
    ///   [`Self::admit_read`](crate::lower::ExpressionsRef::admit_read) refuses
    ///   the read; [`LoweringRefusal::ImplicitUnsupplied`] for a declaration
    ///   with implicits named anywhere but a call supplying them; the
    ///   wrong-sort refusal for a flattened model implicit, which is its
    ///   components and no value (`ModelsRef::unflattened`).
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter named in a result type's compound
    ///   endpoint, and one named in a body, each checked; a module's value
    ///   named in a type member's type, refused.
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_reads_types_and_never_values`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_model_implicit_named_alone_is_refused_739`
    #[spec(
        ensures: |ret| match ret {
            | Err(ref refusal) => match resolved {
                | Resolved::Declaration { .. } => matches!(*refusal, LoweringRefusal::PhaseDependence { .. } | LoweringRefusal::InertRead { .. } | LoweringRefusal::ImplicitUnsupplied { .. }),
                | Resolved::Binder(bound) => self.cx().flattened.contains_key(&bound.binder),
            },
            | Ok(ref plan) => match (resolved, self.cx().in_type.contains(&site.at.node)) {
                | (Resolved::Binder(bound), true) => {
                    matches!(*plan, Plan::StaticApplication(Code::Bound { binder, .. }, arguments) if binder == bound.binder && arguments == FormStretch::default())
                        && (bool::from(self.cx().scope.mentioned(bound.binder)) || self.cx().in_quote.contains(&site.at.node))
                },
                | _ => *plan == resolved.term(),
            },
        },
    )]
    #[inline]
    pub fn resolved_term(
        &mut self,
        site: Site,
        frame: Frame,
        resolved: Resolved,
    ) -> Result<Plan, LoweringRefusal<'source>>
    {
        ModelsRef::new(self.host_ref()).unflattened(site, resolved)?;
        match resolved {
            Resolved::Binder(bound) if self.cx().in_type.contains(&site.at.node) => {
                let telescope = self.name_in_type(site.at.node, bound.binder);
                Ok(Plan::StaticApplication(
                    Code::Bound {
                        from: frame,
                        binder: bound.binder,
                        telescope,
                    },
                    FormStretch::default(),
                ))
            },
            Resolved::Binder(_) => Ok(resolved.term()),
            Resolved::Declaration { constant, .. } => {
                self.shared()
                    .admit_read(site, SlotIndex::from(usize::from(constant)))?;
                self.shared().supplied_or_refused(site, constant)?;
                Ok(resolved.term())
            },
        }
    }

    /// Keep that the name written at `span` resolved to `resolved`: a binder
    /// by its written name, a declaration by its admission position.
    ///
    /// # Specification
    /// - requires: `resolved` is what the name at `span` resolves to.
    /// - ensures: one record of `span` naming the binder's written site, or the
    ///   declaration's admission position, appended to
    ///   [`LoweredModule::resolutions`]; nothing for a binder the source names
    ///   nowhere.
    /// - provides: the use a declaration refused later keeps.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`LoweredModule::resolutions`].
    /// - witness: `gandr-surface-lowering::tests::scopes::a_refused_declaration_keeps_the_names_it_resolved_836`
    #[spec(captures: before = self.cx().resolutions.len(), ensures: self.cx().resolutions.len() <= before.saturating_add(1))]
    #[inline]
    pub fn resolved(
        &mut self,
        span: ByteSpan,
        resolved: Resolved,
    )
    {
        let resolution = match resolved {
            Resolved::Binder(bound) => match self.cx().scope.site(bound.binder) {
                Maybe::Present(site) => crate::Resolution::Binder(site),
                Maybe::Absent(_) => return,
            },
            Resolved::Declaration { constant, .. } => crate::Resolution::Declaration(constant),
        };
        self.cx_mut().resolutions.push((span, resolution));
    }

    /// Keep that the name written at `span` names `constructor`.
    ///
    /// # Specification
    /// - requires: `constructor` is what the name at `span` resolves to.
    /// - ensures: one record of `span` naming the constructor's name tile and
    ///   its family's admission position appended to
    ///   [`LoweredModule::resolutions`]; nothing for a family whose slot was
    ///   not collected.
    /// - provides: the use a declaration refused later keeps.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`LoweredModule::resolutions`].
    /// - witness: `gandr-surface-lowering::tests::scopes::a_refused_declaration_keeps_the_names_it_resolved_836`
    #[spec(captures: before = self.cx().resolutions.len(), ensures: self.cx().resolutions.len() <= before.saturating_add(1))]
    #[inline]
    pub fn constructed_at(
        &mut self,
        span: ByteSpan,
        constructor: crate::module::Constructor,
    )
    {
        let cx = self.cx_mut();
        if let Some(slot) = cx.collected.slots.get(usize::from(constructor.family)) {
            cx.resolutions.push((span, crate::Resolution::Constructor {
                named: constructor.named.span,
                family: slot.constant,
            }));
        }
    }

    /// Record that a type position at `node` names `binder`, and answer the
    /// telescope its index counts in: a type a body quotes counts in its own,
    /// leaving the signature's arrows as they are, and any other type in the
    /// signature's, whose arrow binding `binder` becomes dependent (#547).
    ///
    /// # Specification
    /// - requires: `node` is a type position naming `binder`.
    /// - ensures: [`Telescope::Quote`] with `binder` quoted when `node` lies in
    ///   a body quote; [`Telescope::Signature`] with `binder` mentioned
    ///   otherwise.
    /// - provides: the one place a binder read inside a type chooses its
    ///   telescope.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter only a body quote names leaves its arrow
    ///   independent and the quote reads it; one a signature type names makes
    ///   it dependent.
    /// - witness: `gandr-surface-lowering::lower::tests::a_quote_in_a_body_reads_past_an_unmentioned_parameter`
    #[spec(ensures: |ret| if self.cx().in_quote.contains(&node) {
        ret == Telescope::Quote
    } else {
        ret == Telescope::Signature && bool::from(self.cx().scope.mentioned(binder))
    })]
    #[inline]
    pub fn name_in_type(
        &mut self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Telescope
    {
        if self.cx().in_quote.contains(&node) {
            self.cx_mut().scope.quote(binder);
            Telescope::Quote
        }
        else {
            self.cx_mut().scope.mention(binder);
            Telescope::Signature
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Whether the type at `node`, which introduces `binder`, names it: in the
    /// telescope [`Self::name_in_type`](crate::lower::Expressions::name_in_type) counted the type's reads in, so a type
    /// a body quotes depends on a binder its own reads name, and any other
    /// type on one a signature type names (#583).
    ///
    /// # Specification
    /// - requires: `node` is the type introducing `binder`, or a node inside
    ///   it; every read of the type has been recorded.
    /// - ensures: whether `binder` binds in [`Telescope::Quote`] when `node`
    ///   lies in a body quote, and in [`Telescope::Signature`] otherwise.
    /// - provides: the Π-or-arrow and Σ-or-product decision, in step with the
    ///   indices the type's reads were minted at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent arrow a body quotes, whose codomain names
    ///   its binder, is the Π over it; one whose codomain does not is the plain
    ///   arrow.
    /// - witness: `gandr-surface-lowering::lower::tests::a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names`
    #[spec(ensures: |ret| ret == self.cx().scope.binds(binder, self.telescope_at(node)))]
    #[inline]
    #[must_use]
    pub fn names_own_binder(
        &self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Mentioned
    {
        self.cx().scope.binds(binder, self.telescope_at(node))
    }

    /// The telescope a type at `node` counts its binders in: a body quote's
    /// own when `node` lies in a body quote, the signature's otherwise (#547).
    ///
    /// # Specification
    /// - requires: the classification has reached `node`.
    /// - ensures: [`Telescope::Quote`] exactly when `node` lies in a body
    ///   quote.
    /// - provides: the one choice of telescope every reading of a type's
    ///   binders shares: its indices, its arrows' dependency (#583) and the
    ///   names it is spelled with (#590).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type a body quotes answers the quote's telescope
    ///   and a signature type the signature's: the arrow minted from each, and
    ///   the label spelled for each, tell the two apart.
    /// - witness: `gandr-surface-lowering::lower::tests::a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names`
    #[spec(ensures: |ret| (ret == Telescope::Quote) == self.cx().in_quote.contains(&node))]
    #[inline]
    #[must_use]
    pub fn telescope_at(
        &self,
        node: NodeIndex,
    ) -> Telescope
    {
        if self.cx().in_quote.contains(&node) {
            Telescope::Quote
        }
        else {
            Telescope::Signature
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify a number literal.
    ///
    /// # Specification
    /// - requires: `site` is a number, bare or written with its type suffix.
    /// - ensures: a number standing as a value is planned as the literal of an
    ///   integer width when it is written with that width's suffix and its
    ///   digits fit the width; as a binary64 float when it is written with the
    ///   `f64` suffix or annotated `(n : f64)`, rounded to nearest from its
    ///   decimal text; as the binary natural it names when it is decimal digits
    ///   annotated `(n : Nat)`, `Nat` resolving to the prelude's ([`natural`]);
    ///   a lexeme of decimal digits is planned as its canonical integer; a
    ///   fraction or an exponent with neither suffix nor annotation is planned
    ///   as its exact decimal, which the checker reads at the type it is
    ///   checked at (#4807).
    /// - provides: the literal reading of numbers.
    /// - fails: yields the wrong-sort refusal outside value position; the `f32`
    ///   suffix is a typed number the fragment does not admit; digits that do
    ///   not fit an integer width, or a fraction or an exponent before one, are
    ///   a malformed literal; so is anything but decimal digits annotated `(n :
    ///   Nat)`, and a decimal whose exact value spells more digits than the
    ///   lowering holds; any other text is a malformed literal; the
    ///   annotation's name propagates its resolution's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The number's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — canonical integer magnitudes, each integer width at
    ///   its extremes and one past them, suffixed and annotated floats, the
    ///   `f32` suffix, a bare fraction, numerals at the prelude's `Nat` and at
    ///   a source's own, and malformed lexemes separate each plan from each
    ///   refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::an_integer_literal_is_its_canonical_magnitude`
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_number_takes_float64_from_its_suffix_or_annotation_1830`
    /// - witness: `gandr-surface-lowering::lower::tests::a_typed_number_is_its_value_at_its_width`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decimal_reads_as_its_exact_value_4807`
    /// - witness: `gandr-surface-lowering::lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
    /// - witness: `gandr-surface-lowering::lower::natural::tests::a_numeral_at_a_source_s_own_nat_stays_an_integer_3287`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Literal(Literal::Integer(_) | Literal::Fixed(_) | Literal::Float64(_) | Literal::Numeric(_)) | Plan::Natural(..)))
                )
        },
    )]
    fn number(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let text = self.cx().text_at(site.at);
        let spelled: &str = text.as_ref();
        match typed_number_literal(text) {
            Maybe::Present(literal) => {
                self.plan(site, Plan::Literal(literal));
                return Ok(());
            },
            Maybe::Absent(literal::Absent::OutsideWidth) => {
                return Err(LoweringRefusal::MalformedLiteral {
                    span: site.at.span,
                    form: site.name,
                });
            },
            Maybe::Absent(literal::Absent::Malformed | literal::Absent::NotALiteral) => {},
        }
        if spelled.ends_with("f32") {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::TypedNumber)));
        }
        if let Maybe::Present(naturals) = self.annotated_natural(site, frame)? {
            let Maybe::Present(Literal::Integer(integer)) = parse_literal(Former::Number, text)
            else {
                return Err(LoweringRefusal::MalformedLiteral {
                    span: site.at.span,
                    form: site.name,
                });
            };
            self.plan(site, Plan::Natural(naturals, integer.magnitude().clone()));
            return Ok(());
        }
        let annotated = self
            .cx()
            .classifiers
            .get(&site.at.node)
            .and_then(|&written| self.cx().tree.fragment(written))
            .is_some_and(|written| {
                matches!(
                    type_atom(SurfaceName::from(written)),
                    Maybe::Present(TypeAtom::Float64)
                )
            });
        let suffixed = spelled.strip_suffix("f64");
        if suffixed.is_some() || annotated {
            let Ok(float) = suffixed.unwrap_or(spelled).parse::<Float64Literal>()
            else {
                return Err(LoweringRefusal::MalformedLiteral {
                    span: site.at.span,
                    form: site.name,
                });
            };
            self.plan(site, Plan::Literal(Literal::Float64(float)));
            return Ok(());
        }
        if let Maybe::Present(literal) = parse_literal(Former::Number, text) {
            self.plan(site, Plan::Literal(literal));
            return Ok(());
        }
        // A bare fraction states no type of its own: it lowers to its exact
        // decimal, which the checker reads at the type it is checked at.
        if let Maybe::Present(decimal) = decimal_literal(text) {
            self.plan(site, Plan::Literal(Literal::Numeric(decimal)));
            return Ok(());
        }

        Err(LoweringRefusal::MalformedLiteral {
            span: site.at.span,
            form: site.name,
        })
    }

    /// Classify a string literal.
    ///
    /// # Specification
    /// - requires: `site` is a string; `pieces` is its reading.
    /// - ensures: a string standing as a value with no interpolation is planned
    ///   as its decoded text; a string with an interpolation is planned as
    ///   [`Self::interpolation`](crate::lower::Expressions::interpolation)
    ///   reads it.
    /// - provides: the text half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; a string
    ///   missing a delimiter is a malformed literal; an interpolation refuses
    ///   as [`Self::interpolation`](crate::lower::Expressions::interpolation)
    ///   does.
    /// - panics: none.
    ///
    /// # Errors
    /// The string's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted strings decode their escapes; an interpolated
    ///   string is planned apart from a plain one, and malformed text retains
    ///   its located refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
    /// - witness: `gandr-surface-lowering::lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
    /// - witness: `gandr-surface-lowering::lower::tests::an_interpolated_string_appends_its_segments_in_order`
    /// - witness: `gandr-surface-lowering::lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Literal(Literal::Text(_)) | Plan::Interpolated(..)))
                )
        },
    )]
    fn text(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let interpolated = pieces.pieces.iter().any(
            |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::INTERPOLATION),
        );
        if interpolated {
            return self.interpolation(site, pieces);
        }
        let _frame = self.require(site, Produced::Value)?;
        let Maybe::Present(literal) = parse_literal(Former::Text, self.cx().text_at(site.at))
        else {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        };

        self.plan(site, Plan::Literal(literal));

        Ok(())
    }

    /// Classify a character literal.
    ///
    /// # Specification
    /// - requires: `site` is a character.
    /// - ensures: a character standing as a value is planned as the one scalar
    ///   between its quotes, its escape decoded as a string's is.
    /// - provides: the character half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; a
    ///   character whose quotes hold no scalar, or more than one, once decoded,
    ///   is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The character's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain, an escaped and a multibyte character lower
    ///   to their scalars, and an escaped line break, which decodes to nothing,
    ///   is refused as malformed.
    /// - witness: `gandr-surface-lowering::lower::tests::a_character_literal_is_the_scalar_between_its_quotes`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lexeme_of_the_wrong_shape_parses_to_nothing`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&Plan::Literal(Literal::Character(_)))
                )
        },
    )]
    fn character(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let Maybe::Present(literal) = parse_literal(Former::Character, self.cx().text_at(site.at))
        else {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        };
        self.plan(site, Plan::Literal(literal));
        Ok(())
    }

    /// Classify a string holding an interpolation `"…${ e }…"`.
    ///
    /// # Specification
    /// - requires: `site` is a string; `pieces` is its reading and holds an
    ///   interpolation opener.
    /// - ensures: the string is planned as a computation over its segments in
    ///   written order: each run of text between a quote, an opener and a
    ///   closer with its escapes decoded as one, and each interpolated
    ///   expression read as a value under the string's frame. An empty run is
    ///   no segment.
    /// - provides: the reading the mint folds into `string.append` calls.
    /// - fails: yields the wrong-sort refusal where a computation may not
    ///   stand; a string missing its closing quote is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The string's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a string opening and closing on text, one opening on
    ///   an interpolation and one holding a lone interpolation are each
    ///   asserted as the exact append chain they mint.
    /// - witness: `gandr-surface-lowering::lower::tests::an_interpolated_string_appends_its_segments_in_order`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Interpolated(..)))
        },
    )]
    fn interpolation(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        use gandr_core_term::primitive::PRELUDE;
        let frame = self.require(site, Produced::Computation)?;
        let closed = matches!(
            (pieces.pieces.first(), pieces.pieces.last()),
            (Some(&Piece::Tile { label: opened, .. }), Some(&Piece::Tile { label: closing, .. }))
                if pieces.pieces.len() > 1 && opened == TileName::QUOTE && closing == TileName::QUOTE
        );
        if !closed {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        }
        let Some(&append) = PRELUDE
            .iter()
            .find(|row| row.name().as_ref() == "string.append")
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Interpolation)));
        };
        let start = self.cx().segments.mark();
        let mut run = String::new();
        for &piece in &pieces.pieces {
            match piece {
                Piece::Tile { label, at }
                    if label == TileName::STRING_FRAGMENT || label == TileName::ESCAPE_SEQUENCE =>
                {
                    run.push_str(self.cx().text_at(at).as_ref());
                },
                Piece::Tile { .. } => {
                    if !run.is_empty() {
                        let decoded = decode_escapes(SourceFragment::from(run.as_str()));
                        self.cx_mut()
                            .segments
                            .push(TextSegment::Text(StringLiteral::new(decoded)));
                        run.clear();
                    }
                },
                Piece::Operand(operand) => {
                    self.read(operand.node, Reading::Value(frame));
                    self.cx_mut()
                        .segments
                        .push(TextSegment::Operand(operand.node));
                },
            }
        }
        let segments = self.cx().segments.since(start);

        self.plan(site, Plan::Interpolated(append, segments));

        Ok(())
    }

    /// Classify a parenthesised expression: a grouping, a pair or an
    /// annotation.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised expression in term position.
    /// - ensures: `(e)` reads its operand at its own reading and adopts it, the
    ///   answer its position states passed on; a comma list is read as a pair;
    ///   a labelled group as `Models::labelled_outputs` reads it; `()` ending a
    ///   body of no outputs returns none; `(e : T)` is read as
    ///   `Native::annotated` reads it, adopting a constructor that takes `T` as
    ///   its classifier, or the value an ascription its position makes carries,
    ///   and otherwise planned as a value ascription, an injection among them,
    ///   its label read in the sum `T` states.
    /// - provides: the reading of every form the grammar folds into
    ///   parentheses.
    /// - fails: yields the pair's own refusal, the annotation's refusal as
    ///   `Native::annotated` states it, the empty-list refusal for `()`, which
    ///   is never the unit, and the extra-operand refusal for a juxtaposition.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — grouping preserves its operand while a
    ///   comma-separated tuple plans one tuple rather than treating the commas
    ///   as grouping, and an annotation no form carries plans its ascription.
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::the_empty_parentheses_are_never_the_unit`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotation_no_form_carries_is_a_value_ascription_1543`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Transparent(_) | Plan::Tuple(_) | Plan::ReturnAll(_) | Plan::Ascribed(..)))
                )
        },
    )]
    fn parenthesized(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let list = cursor.clone();
        let _open = cursor.tile(TileName::PAREN_OPEN);
        if let Maybe::Present(_) = cursor.at(TileName::DOT) {
            return Models::new(self.host()).labelled_outputs(site, list);
        }
        let run = cursor.operands();
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return self.pair(site, list);
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return Native::new(self.host()).annotated(site, run, cursor);
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        if let Run::Empty(_) = run {
            // `()` ending a body of no outputs returns none.
            if Models::new(self.host())
                .answered_outputs(site)?
                .is_some_and(|outputs| outputs.is_empty())
            {
                let _frame = self.require(site, Produced::Computation)?;
                self.plan(site, Plan::ReturnAll(FormStretch::default()));
                return Ok(());
            }
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        let inner = site.one(run)?;
        self.group(site, inner);
        self.read(inner.node, site.reading);
        if let Some(&answer) = self.cx().answers.get(&site.at.node) {
            let _passed = self.cx_mut().answers.insert(inner.node, answer);
        }
        if let Some(&inherited) = self.cx().inherited.get(&site.at.node) {
            let _passed = self.cx_mut().inherited.insert(inner.node, inherited);
        }
        Exits::new(self.host()).pass_paths(site.at.node, inner.node);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Record that the grouping at `site` wraps `inner`.
    ///
    /// # Specification
    /// - requires: `inner` is the one operand of the grouping at `site`.
    /// - ensures: `inner` is held against the outermost grouping around it: the
    ///   one `site` is held against when `site` is itself grouped, else `site`.
    /// - provides: the place
    ///   [`Self::standing`](crate::lower::ExpressionsRef::standing) refuses a
    ///   grouped form at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a form under one grouping, under two nested ones and
    ///   under a type quote is held against the outermost.
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouped_form_of_the_wrong_sort_is_refused_at_its_parentheses_2341`
    #[spec(ensures: |()| self.cx().grouped.contains_key(&inner.node))]
    fn group(
        &mut self,
        site: Site,
        inner: Placed,
    )
    {
        let outermost = self
            .cx()
            .grouped
            .get(&site.at.node)
            .copied()
            .unwrap_or(site.at);
        let _held = self.cx_mut().grouped.insert(inner.node, outermost);
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The form that stands in `site`'s position: the outermost grouping
    /// around it, which is what the position reads, else the form itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `site` placed at the grouping
    ///   [`Self::group`](crate::lower::Expressions::group) held it against, its
    ///   name and reading kept; `site` itself when no grouping wraps it.
    /// - provides: where a form of the wrong sort is refused, so the refusal
    ///   marks the bytes the position holds: `loop { (n) }`, its `break` left
    ///   out, is refused at `(n)`, which touches where `break` stood.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a grouped value read as a computation and a grouped
    ///   computation type read as a value type are refused at the parentheses,
    ///   an ungrouped one at itself.
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouped_form_of_the_wrong_sort_is_refused_at_its_parentheses_2341`
    #[spec(ensures: |ret| ret.name == site.name && ret.reading == site.reading
        && ret.at == self.cx().grouped.get(&site.at.node).copied().unwrap_or(site.at))]
    fn standing(
        &self,
        site: Site,
    ) -> Site
    {
        match self.cx().grouped.get(&site.at.node) {
            Some(&outermost) => Site {
                at: outermost,
                ..site
            },
            None => site,
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify a type quote, `type(T)`: the code of `T` where an expression
    /// stands.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `type(` of a type quote.
    /// - ensures: the one type is read at the quote's own reading and adopted,
    ///   so a type where a value is read is quoted at its own sort, as a type
    ///   written bare there is; a term form quoted, other than a name or a
    ///   constructor, which may name a type, is refused as the wrong sort for a
    ///   type, at the outermost grouping around it: the quote.
    /// - provides: the types an expression cannot spell bare — a receive `?(S).
    ///   T` and a labelled sum `+{ … }` — as arguments.
    /// - fails: yields the one-operand refusal and the unclosed-form fault,
    ///   both naming the quote, the wrong-sort refusal of a quoted term, and
    ///   the type's own refusal at its reading.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a receive, a labelled sum and a computation type
    ///   quoted as arguments lower to the exact core codes a bare type there
    ///   lowers to; a block quoted, `type({Unit})` with its sum's `+` left out,
    ///   is refused at the quote, which touches where the `+` stood.
    /// - witness: `gandr-surface-lowering::lower::tests::a_quoted_type_is_the_code_a_bare_type_is`
    /// - witness: `gandr-surface-lowering::lower::tests::a_quoted_term_is_refused_at_its_quote_2341`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Transparent(child)) if self.cx().reading(child) == site.reading)
        },
    )]
    fn type_quote(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::TYPE_QUOTE_OPEN);
        let inner = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        self.group(site, inner);
        // A term quoted where a type is spelled: `type({Unit})`, the sum's `+`
        // left out, reads a block the quote does not take, so the block is
        // refused at the quote rather than entered and its statement refused
        // inside it, away from the `+` (#2341).
        if let Some(node) = self.cx().tree.node(inner.node)
            && let Ok(Shape::Form { name, former }) = shape_of(self.cx().pbg, node)
            && family_of(former) == Family::Term
            && !matches!(former, Former::Name | Former::Constructor)
        {
            let quoted = Site {
                at: inner,
                name,
                reading: Reading::ValueType(site.reading.frame()),
            };
            return Err(self
                .shared()
                .standing(quoted)
                .out(FragmentBoundary::WrongSort));
        }
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Classify a tuple, `(v1, …, vn)`, the one-element `(v,)` included, or,
    /// ending a body whose result is a group of outputs, the return of one
    /// value per output.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `(` of a parenthesised expression
    ///   whose first member a comma follows.
    /// - ensures: ending a body whose written result is a group of outputs, as
    ///   `Models::answered_outputs` reads it, the tuple stands as a computation
    ///   and is planned as the return of its members; otherwise it stands as a
    ///   value and is planned over them as one tuple, as one `*` chain is one
    ///   product. Either way every member is read as a value under its own
    ///   frame. At a product it is written or answered at, as
    ///   [`Self::stated_value`] reads it, of as many positional components as
    ///   it has members, each member written as a constructor, a call, a list
    ///   or a parenthesised form takes the component at its place, as
    ///   [`Self::classify_member`] gives it.
    /// - provides: the introduction of the eager product, and the return of
    ///   several values.
    /// - fails: yields the wrong-sort refusal where no value is read, and the
    ///   list's refusal for a member out of shape, both naming the tuple; the
    ///   walk's refusal reading the product.
    /// - panics: none.
    ///
    /// # Errors
    /// The tuple's refusal.
    ///
    /// # Termination
    /// The member loop runs once per entry of the finite member stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of one, of two and of three, and a tuple
    ///   where a computation is read, each asserted as the exact core node read
    ///   back out of the arena or the exact refusal; tuples of a parameterised
    ///   family's constructors under an annotation, at a body's tail and inside
    ///   a list, each classified by its component; and a tuple ending a body
    ///   that returns two outputs.
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_tuple_gives_its_members_the_product_s_components_1877`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_tuple_ending_a_body_of_outputs_returns_each_member`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Tuple(members) | Plan::ReturnAll(members))) if members != FormStretch::default()
                )
        },
    )]
    fn pair(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let tuple = Site {
            name: FormName::TUPLE,
            ..site
        };
        let outputs = Models::new(self.host()).answered_outputs(site)?;
        let produced = match outputs {
            Some(_) => Produced::Computation,
            None => Produced::Value,
        };
        let frame = self.require(tuple, produced)?;
        let start = self.cx().operands.entries().len();
        if let Err(refusal) = arguments(tuple, &mut cursor, &mut self.cx_mut().operands) {
            self.cx_mut().operands.truncate(At::from(start));
            return Err(refusal);
        }
        let members = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        if outputs.is_none() {
            self.classify_members(tuple, members, frame)?;
        }
        for position in members.start .. members.end {
            if let Some(&member) = self.cx().operands.entries().get(position) {
                self.read(member, Reading::Value(frame));
            }
        }

        let members = self.cx().kept(members);
        self.plan(site, match outputs {
            Some(_) => Plan::ReturnAll(members),
            None => Plan::Tuple(members),
        });

        Ok(())
    }

    /// Classify a list literal, `#[v1, …, vn]`, the empty `#[]` included.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `#[` of a list literal.
    /// - ensures: the list stands as a value, reads every element as a value
    ///   under its own frame, and is planned over them as one native list, as
    ///   `v1 :: … :: vn :: nil` is. Under a written classifier `List(T)` — its
    ///   annotation, or the signature of the definition it is — its parentheses
    ///   stripped, each element written as a constructor, a call, a list or a
    ///   parenthesised form takes `T` as its own, as a constructor's field
    ///   gives the constructor written in it its type. A list ending a body
    ///   that answers `-F List(T)` or returns `List(T)`, or carried such an
    ///   answer by the list or tuple it is a member of, gives each such element
    ///   `T` as the answer it returns, read under the answer's frame and
    ///   carried to the list's.
    /// - provides: the introduction of the native list from its elements.
    /// - fails: yields the wrong-sort refusal where no value is read, and the
    ///   element list's refusal for an element out of shape, both naming the
    ///   list; the walk's refusal reading the classifier.
    /// - panics: none.
    ///
    /// # Errors
    /// The list's refusal.
    ///
    /// # Termination
    /// The element loop runs once per entry of the finite element stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty list, a list of one and a list of three,
    ///   each asserted as the exact cons chain read back out of the arena; a
    ///   list where a computation is read refused; and a list of a
    ///   parameterised family's constructors, and a list of such lists, under
    ///   their annotation and at a body's tail, each constructor classified by
    ///   the element type.
    /// - witness: `gandr-surface-lowering::lower::tests::a_list_literal_lowers_to_its_cons_cells_1544`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_listed_constructor_takes_the_element_type_1544`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_listed_constructor_takes_the_answered_element_type_1602`
    #[spec(
        ensures: |ret| ret.is_err() || matches!(self.cx().plans.get(site.at.node), Some(&Plan::List(_))),
    )]
    fn list(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let start = self.cx().operands.entries().len();
        if let Err(refusal) = delimited(
            site,
            &mut cursor,
            &mut self.cx_mut().operands,
            TileName::SEQUENCE_OPEN,
            TileName::BRACKET_CLOSE,
        ) {
            self.cx_mut().operands.truncate(At::from(start));
            return Err(refusal);
        }
        let elements = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        // An element type the list is written at classifies each constructor,
        // call, list or tuple among its elements, as a field's type does the
        // constructor written in it; one the list answers is carried to them as
        // the answer each returns.
        let (stated, answered) = self.stated_value(site)?;
        if let Some(stated) = stated
            && let Maybe::Present(typed) = Native::new(self.host()).unwrapped(stated)?
            && typed.former == Former::TypeApplication
            && typed.keyword.is_some_and(|head| {
                self.cx().former(self.cx().name_at(head)) == Maybe::Present(TypeFormer::List)
            })
            && let [element_type] = typed.operands[..]
        {
            for position in elements.start .. elements.end {
                if let Some(&element) = self.cx().operands.entries().get(position) {
                    self.classify_member(element, element_type, answered, frame);
                }
            }
        }
        for position in elements.start .. elements.end {
            if let Some(&element) = self.cx().operands.entries().get(position) {
                self.read(element, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::List(self.cx().kept(elements)));

        Ok(())
    }

    /// The value type an answer returns, as the node that writes it: the
    /// returned type of a written `-F A`, a written list or product type the
    /// lowering inserts the returner over, or the type a returning answer
    /// writes.
    ///
    /// # Specification
    /// - requires: nothing beyond a well-formed tree.
    /// - ensures: the operand of the answer's node, its parentheses stripped,
    ///   when the answer is written and the node a returner type of one
    ///   operand; the node, its parentheses stripped, when the answer is
    ///   written as a type application or a product type, `-> List(T)` or `->
    ///   (A * B)`; the node itself when the answer returns it; nothing for a
    ///   loop arm's, a valued answer or another written type.
    /// - fails: the walk's refusal reading the node.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result `-F List(T)`, `-> List(T)` and a
    ///   thunk signed `() -> List(T)`, each giving a listed constructor its
    ///   element type, and a function result `-F (A * B)` or `-> (A * B)`
    ///   giving a tuple's members theirs.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_listed_constructor_takes_the_answered_element_type_1602`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_tuple_gives_its_members_the_product_s_components_1877`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |node| match answer.over {
        native::Over::Returning => *node == Some(answer.node),
        native::Over::Written => true,
        native::Over::Loop { .. } | native::Over::Valued { .. } => node.is_none(),
    }))]
    fn answered_value(
        &mut self,
        answer: native::Answer,
    ) -> Result<Option<NodeIndex>, LoweringRefusal<'source>>
    {
        match answer.over {
            native::Over::Returning => Ok(Some(answer.node)),
            native::Over::Written => match Native::new(self.host()).unwrapped(answer.node)? {
                Maybe::Present(returner) if returner.former == Former::ReturnerType => {
                    match *returner.operands.as_slice() {
                        [returned] => Ok(Some(returned)),
                        _ => Ok(None),
                    }
                },
                // A list's or a product's type written at a result without
                // its returner, `-> List(T)` or `-> (A * B)`, is the value type
                // the returner the lowering inserts there returns: neither
                // former writes a computation type.
                Maybe::Present(written)
                    if matches!(
                        written.former,
                        Former::TypeApplication | Former::ProductType
                    ) =>
                {
                    Ok(Some(written.node))
                },
                Maybe::Present(_) | Maybe::Absent(_) => Ok(None),
            },
            native::Over::Loop { .. } | native::Over::Valued { .. } => Ok(None),
        }
    }

    /// The type a list or a tuple at `site` is written at, and the answer it
    /// was read off when it is answered rather than written.
    ///
    /// # Specification
    /// - requires: `site` is a list or a tuple standing as a value.
    /// - ensures: its written classifier — its annotation, the signature of the
    ///   definition it is, or one the form around it passes — with no answer;
    ///   else the value type the answer an enclosing form carries returns, or
    ///   the answer of the body it ends, as [`Self::answered_value`] reads it,
    ///   with that answer; else nothing.
    /// - fails: as [`Self::answered_value`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::answered_value`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::answered_value`], and an annotated list
    ///   and tuple, each classifying its members by what it is written at.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_listed_constructor_takes_the_element_type_1544`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_tuple_gives_its_members_the_product_s_components_1877`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(_, ref answered)| answered.is_none() || !self.cx().classifiers.contains_key(&site.at.node)))]
    #[inline]
    pub fn stated_value(
        &mut self,
        site: Site,
    ) -> Result<(Option<NodeIndex>, Option<native::Answer>), LoweringRefusal<'source>>
    {
        Ok(
            match (
                self.cx().classifiers.get(&site.at.node),
                self.cx().inherited.get(&site.at.node),
            ) {
                (Some(&written), _) | (None, Some(&native::Classifier::Written(written))) => {
                    (Some(written), None)
                },
                (None, Some(&native::Classifier::Answered { answer, .. })) => {
                    (self.answered_value(answer)?, Some(answer))
                },
                (None, Some(_)) => (None, None),
                (None, None) => match self
                    .cx()
                    .answers
                    .get(&site.at.node)
                    .filter(|_| self.cx().exits.contains(&site.at.node))
                {
                    Some(&answer) => (self.answered_value(answer)?, Some(answer)),
                    None => (None, None),
                },
            },
        )
    }

    /// Give each member of the eager product at `site` the component its
    /// stated product writes at the member's place.
    ///
    /// # Specification
    /// - requires: `site` is a tuple or a positional telescope value standing
    ///   as a value; `members` are its members in written order, and `frame` is
    ///   theirs.
    /// - ensures: when the type `site` is written or answered at states a
    ///   product of as many positional components as `members`, each member
    ///   takes its component as [`Self::classify_member`] gives it; otherwise
    ///   no member changes.
    /// - fails: as [`Self::stated_value`] and `Models::stated_entries`.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::stated_value`] and `Models::stated_entries`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::classify_member`], for the tuple and for
    ///   the positional telescope value alike.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_tuple_gives_its_members_the_product_s_components_1877`
    #[spec(
        captures: before = (self.cx().classifiers.len(), self.cx().inherited.len()),
        ensures: |ret| ret.is_err() || (self.cx().classifiers.len() >= before.0 && self.cx().inherited.len() >= before.1),
    )]
    #[inline]
    pub fn classify_members(
        &mut self,
        site: Site,
        members: Stretch,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let (stated, answered) = self.stated_value(site)?;
        if let Some(stated) = stated
            && let Maybe::Present(components) = Models::new(self.host()).stated_entries(
                site,
                stated,
                Former::TelescopeType,
                arity::Thunked(false),
            )?
            && components.len() == members.end.saturating_sub(members.start)
            && components
                .iter()
                .all(|component| matches!(component.key, arity::Key::Positional))
        {
            for (position, component) in (members.start .. members.end).zip(&components) {
                if let Some(&member) = self.cx().operands.entries().get(position) {
                    self.classify_member(member, component.held.at().node, answered, frame);
                }
            }
        }

        Ok(())
    }

    /// Give `member`, a list's element or an eager product's member, the type
    /// `component` writes, when it is a form that takes one.
    ///
    /// # Specification
    /// - requires: `component` is read under `answered`'s frame when `answered`
    ///   is present, else under the frame its written classifier was read in;
    ///   `frame` is the member's.
    /// - ensures: a member written as a constructor, a call, a list, a
    ///   positional telescope value or a parenthesised form takes `component`
    ///   as its written classifier when `answered` is absent, and otherwise
    ///   inherits the answer returning `component` under `answered`'s frame,
    ///   carried to `frame`; any other member is left as it was.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated_value`].
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_listed_constructor_takes_the_answered_element_type_1602`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_tuple_gives_its_members_the_product_s_components_1877`
    #[spec(
        captures: before = (self.cx().classifiers.len(), self.cx().inherited.len()),
        ensures: self.cx().classifiers.len() >= before.0 && self.cx().inherited.len() >= before.1,
    )]
    fn classify_member(
        &mut self,
        member: NodeIndex,
        component: NodeIndex,
        answered: Option<native::Answer>,
        frame: Frame,
    )
    {
        let takes = self.cx().tree.node(member).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Constructor
                        | Former::Call
                        | Former::List
                        | Former::Telescope
                        | Former::Parenthesized,
                    ..
                })
            )
        });
        if !takes {
            return;
        }
        match answered {
            Some(answer) => {
                let carried = native::Classifier::Answered {
                    answer: native::Answer {
                        node: component,
                        frame: answer.frame,
                        over: native::Over::Returning,
                        arm: answer.arm,
                    },
                    frame,
                };
                let _first = self.cx_mut().inherited.insert(member, carried);
            },
            None => {
                let _first = self.cx_mut().classifiers.insert(member, component);
            },
        }
    }

    /// Classify a thunk, `thunk { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk in term position.
    /// - ensures: a thunk standing as a value reads its block in its own frame
    ///   as a body a path runs through, answering the type the signature of the
    ///   definition it is states for its body, and is planned over it.
    /// - provides: the value former that suspends a computation.
    /// - fails: yields the wrong-sort refusal outside value position, the
    ///   unadmitted refusal for a grade, the block's own refusal, and the
    ///   unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The thunk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk keeps its block computation under suspension;
    ///   an authored force reads that value before forcing its computation.
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Thunk(Block { statements, .. })) if self.cx().statements.whole(statements).is_some())
        },
    )]
    fn thunk(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::THUNK);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(
                FormName::GRADE,
                FragmentBoundary::Unadmitted(Unbuilt::ThunkGrade),
            ));
        }
        let body = self.block(site, &mut cursor, frame)?;
        let answer = match self.cx().thunked.get(&site.at.node) {
            Some(&answer) => {
                let _passed = self.cx_mut().answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        Exits::new(self.host()).open_body(site, body, answer)?;

        self.plan(site, Plan::Thunk(body));

        Ok(())
    }

    /// Classify a lambda, `fun (x) { … }` or `fun (x : A) { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: a lambda standing as a computation binds its one parameter in
    ///   a frame extending its own, reads its block under that frame as a body
    ///   a path runs through, and is planned over it. Where its position
    ///   answers a written arrow `A -> C`, parentheses stripped, the binder is
    ///   typed `A` as a parameter's written type types it, and the body answers
    ///   `C`, each under the frame the arrow was read under. A parameter
    ///   written with its type `A` reads `A` as a value type under the frame
    ///   the lambda stands in, binds the parameter typed `A`, and reads its
    ///   block beneath one more binder, unnamed: the bind the mint ascribes the
    ///   argument at, recorded with `A` (#3735). A lambda `cong` maps a path
    ///   by, untyped and unanswered, types its binder with the carrier its
    ///   path's written type states (#3773). A bare lambda passed for a
    ///   parameter, its binder written untyped, records its binder in
    ///   [`Context::argued_binders`](gandr_surface_lowering_base::lower::Context::argued_binders)
    ///   with the parameter and the arrow's domain (#3921). A matching lambda,
    ///   `fun { | … }`, is `Native::matching_lambda`'s, and a lambda its
    ///   position reads as a type operator ([`Self::static_at`]) is
    ///   [`Self::static_lambda`]'s.
    /// - provides: the binder of the fragment.
    /// - fails: yields the wrong-sort refusal where no bridge reaches a
    ///   computation; the unadmitted refusal for a type abstraction; the arity
    ///   refusal for any parameter count but one; the block's own refusal; and
    ///   the unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body uses its newly introduced binder and a
    ///   lambda offered directly in value position is nested; a typed parameter
    ///   is the argument returned at its written type and bound.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_typed_parameter_binds_its_argument_ascribed_1310`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_lambda_as_congs_function_is_a_function_of_the_paths_points_3773`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_call_s_lambda_argument_reads_its_parameter_s_domain_3921`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Lambda(Block { statements, .. }, _)) if self.cx().statements.whole(statements).is_some())
                || matches!(self.cx().plans.get(site.at.node), Some(&(Plan::Case(_) | Plan::StaticLambda(_))))
        },
    )]
    fn lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // `fun { | … }` matches its binders by clauses.
        let mut ahead = cursor.clone();
        let _keyword = ahead.tile(TileName::FUN);
        if let Maybe::Present(_) = ahead.at(TileName::BRACE_OPEN) {
            return Native::new(self.host()).matching_lambda(site, cursor);
        }
        // A lambda standing where a static former is read is a type operator
        // (#4508).
        if let Some(classifier) = self.static_at(site)? {
            return self.static_lambda(site, cursor, classifier);
        }
        let frame = self.require(site, Produced::Computation)?;
        let _keyword = cursor.tile(TileName::FUN);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(
                FormName::TYPE_ABSTRACTION,
                FragmentBoundary::Unadmitted(Unbuilt::TypeAbstraction),
            ));
        }
        let (binder, declared) = parameter(site, &mut cursor)?;
        let name = self.cx().name_at(binder);
        self.note_binder(binder, frame, name)?;
        let arrow = self.answered_arrow(site)?;
        let unnamed = Maybe::Absent(binder_site::Absent::Unwritten);
        if let Some(declared) = declared {
            // Read where the lambda stands: the parameter is not in scope in
            // its own type.
            self.read(declared.node, Reading::ValueType(frame));
        }
        // A lambda passed for a parameter whose type names the callee's own
        // parameters takes its binder's type from the parameter's domain, which
        // an operation over the binder reads at the call's arguments; nothing
        // answers its body (#3921).
        let argued = match (
            declared,
            arrow,
            self.cx().dependent_answers.get(&site.at.node).copied(),
            self.cx().parameter_typed.get(&site.at.node).copied(),
        ) {
            (None, None, Some(answer), Some(called)) => {
                self.arrow_of(answer)?.map(|(domain, _)| (called, domain))
            },
            _ => None,
        };
        // A lambda `cong` maps by takes the carrier its path's type states
        // (#3773).
        let typed = declared
            .map(|declared| declared.node)
            .or_else(|| arrow.map(|(domain, _)| domain))
            .or_else(|| argued.map(|(_, domain)| domain))
            .or_else(|| self.cx().over_points.get(&site.at.node).copied());
        let bound = match typed {
            Some(declared) => {
                self.cx_mut()
                    .scope
                    .extend_typed(frame, name, declared, Maybe::Present(binder.span))
            },
            None => self
                .cx_mut()
                .scope
                .extend(frame, name, Maybe::Present(binder.span)),
        };
        let extended = Frame::Inner(bound);
        if let Some((called, domain)) = argued {
            let _first = self
                .cx_mut()
                .argued_binders
                .insert(bound, (called, domain, frame));
        }
        // A typed parameter's body stands beneath the bind that holds the
        // argument to its type, whose own binder no name reads (#3735).
        let under = declared.map_or(extended, |declared| {
            let _first = self
                .cx_mut()
                .typed_parameters
                .insert(binder.node, (declared.node, frame, extended));
            Frame::Inner(
                self.cx_mut()
                    .scope
                    .extend(extended, SurfaceName::from(""), unnamed),
            )
        });
        let body = self.block(site, &mut cursor, under)?;
        let answer = match arrow {
            Some((_, codomain)) => {
                let _passed = self.cx_mut().answers.insert(body.last, codomain);
                Maybe::Present(codomain)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        Exits::new(self.host()).open_body(site, body, answer)?;

        self.plan(site, Plan::Lambda(body, binder.node));

        Ok(())
    }

    /// The domain and the answered codomain of the arrow the lambda at `site`
    /// answers: a written arrow `A -> C`, parentheses stripped, or the next
    /// arrow a box `(A1, …, An) -> B` stands for. A binder
    /// the arrow or the space names, `(x : A)`, answers its type `A`. A lambda
    /// a signed definition writes bare, `def f = fun (x) { … }`, answers what
    /// the thunk the checker inserts around it would hand its body, and so does
    /// a lambda a `return` or a tail's `pure` returns where the body answers a
    /// written value function space. The binder's type takes the declaration
    /// its answer belongs to before the walk reaches it
    /// ([`Self::own_written`]), so a name in it resolves where the body reads
    /// it.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: for a position answering a written type that unwraps to an
    ///   arrow of two operands, the domain's node — the type a dependent
    ///   arrow's binder declares — and the codomain answered under the arrow's
    ///   frame; for a position answering an alias's arrows past `t` domains,
    ///   its domain `t + 1` — the type a telescope's entry `t + 1` declares —
    ///   and, under the same frame, the arrows past `t + 1` domains, or `B`
    ///   returning past the last; for a lambda returned where a written value
    ///   function space is answered, as for that space's arrows past no domain;
    ///   nothing for an unanswered position, an answer over a loop or a
    ///   returner, an alias with no domain left and any other type.
    /// - fails: as `Native::unwrapped` and `Models::alias_domains`.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda signed `+U (Empty -> -F Integer)` matches no
    ///   arm on its binder, as a parameter of the same type does, written in a
    ///   thunk or bare, and a lambda signed `Empty => Integer`, `(Empty,
    ///   Integer) => Integer` or the telescope `(a : One) => Path[.A = One](a,
    ///   a)` lowers as under the thunked arrows the alias stands for.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_match_of_no_arms_switches_on_a_lambda_binder_its_arrow_types`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_bare_signed_lambda_s_binder_is_typed_as_in_its_thunk_1944`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_lambda_under_a_telescope_alias_lowers_as_under_its_dependent_arrows_815`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_a_typed_let_s_type_and_a_lambda_s_codomain_5035`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |arrow| arrow.is_none_or(|(_, codomain)| matches!(codomain.over, native::Over::Written | native::Over::Returning | native::Over::Valued { .. }))))]
    fn answered_arrow(
        &mut self,
        site: Site,
    ) -> Result<Option<(NodeIndex, native::Answer)>, LoweringRefusal<'source>>
    {
        let answer = match (
            self.cx()
                .answers
                .get(&site.at.node)
                .or_else(|| self.cx().thunked.get(&site.at.node)),
            self.cx().inherited.get(&site.at.node),
        ) {
            (Some(&answer), _) => answer,
            // A returned lambda is the value of the space the body answers,
            // the thunk the checker inserts around it.
            (
                None,
                Some(&native::Classifier::Answered {
                    answer:
                        answer @ native::Answer {
                            over: native::Over::Written,
                            ..
                        },
                    ..
                }),
            ) => native::Answer {
                over: native::Over::Valued { taken: 0_usize },
                ..answer
            },
            (None, _) => return Ok(None),
        };
        self.arrow_of(answer)
    }

    /// The domain and the answered codomain of the arrow `answer` answers, as
    /// [`Self::answered_arrow`] reads them.
    ///
    /// # Specification
    /// - requires: `answer` answers a lambda in term position.
    /// - ensures: as [`Self::answered_arrow`] for a position `answer` answers.
    /// - fails: as `Native::unwrapped` and `Models::alias_domains`.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::answered_arrow`], and a lambda passed for
    ///   a parameter whose type names the parameters before it, its box written
    ///   with either arrow.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_call_s_lambda_argument_reads_its_parameter_s_domain_3921`
    /// - witness: `gandr-surface-lowering::lower::tests::a_box_passes_a_lambda_applies_states_a_motive_and_matches_its_columns_4853`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |arrow| arrow.is_none_or(|(_, codomain)| matches!(codomain.over, native::Over::Written | native::Over::Returning | native::Over::Valued { .. }))))]
    #[inline]
    pub fn arrow_of(
        &mut self,
        answer: native::Answer,
    ) -> Result<Option<(NodeIndex, native::Answer)>, LoweringRefusal<'source>>
    {
        let taken = match answer.over {
            native::Over::Written => None,
            native::Over::Valued { taken } => Some(taken),
            native::Over::Loop { .. } | native::Over::Returning => return Ok(None),
        };
        let unwrapped = Native::new(self.host()).unwrapped(answer.node)?;
        let Maybe::Present(native::Unwrapped {
            node: written,
            former,
            ref operands,
            ..
        }) = unwrapped
        else {
            return Ok(None);
        };
        let &[domain, codomain] = operands.as_slice()
        else {
            return Ok(None);
        };
        let Some(taken) = taken
        else {
            if former != Former::ArrowType {
                return Ok(None);
            }
            let bound = Models::new(self.host())
                .binder_type(domain, answer.frame)?
                .unwrap_or(domain);
            self.own_written(bound, answer.node);
            return Ok(Some((bound, native::Answer {
                node: codomain,
                ..answer
            })));
        };
        // A value the parameter takes is typed by the box, either arrow
        // writing it.
        if !self.boxes(written)?.0 {
            return Ok(None);
        }
        let Some(domains) = Models::new(self.host()).alias_domains(domain, answer.frame)?
        else {
            return Ok(None);
        };
        let Some(&bound) = domains.get(taken)
        else {
            return Ok(None);
        };
        self.own_written(bound, answer.node);
        let next = taken.saturating_add(1_usize);
        let rest = if next < domains.len() {
            native::Answer {
                over: native::Over::Valued { taken: next },
                ..answer
            }
        }
        else {
            native::Answer {
                node: codomain,
                frame: answer.frame,
                over: native::Over::Returning,
                arm: answer.arm,
            }
        };

        Ok(Some((bound, rest)))
    }

    /// Classify a block standing as a computation, `{ let x = c ; … c }`.
    ///
    /// # Specification
    /// - requires: `site` is a block in term position.
    /// - ensures: a block standing as a computation reads its statements and
    ///   its last computation as a thunk's or a lambda's block does, under its
    ///   own frame, passes the answer its position states and the paths through
    ///   its position to its last computation, runs the paths on to its
    ///   statements when a path passes it, and is planned over them.
    /// - provides: sequencing where one computation is read, a match arm's body
    ///   among them.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   block's own refusal, and the unreachable refusal for statements after
    ///   one every path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block arm binds its statement over its last
    ///   computation, and a block where a value is read is refused.
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_standing_as_a_computation_binds_its_statements`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Block(Block { statements, .. })) if self.cx().statements.whole(statements).is_some())
        },
    )]
    fn sequenced(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let body = self.block(site, &mut cursor, frame)?;
        let answer = match self.cx().answers.get(&site.at.node) {
            Some(&answer) => {
                let _passed = self.cx_mut().answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        Exits::new(self.host()).pass_paths(site.at.node, body.last);
        if self.cx().exitable.contains(&site.at.node) {
            Exits::new(self.host()).paths_through(site, body, answer)?;
        }

        self.plan(site, Plan::Block(body));

        Ok(())
    }

    /// Classify a function tail, `def f(x: A, …) -> B { … }` or `def f(x: A,
    /// …) -> B = e ;`.
    ///
    /// # Specification
    /// - requires: `site` is a declaration form read as a function, whose tail
    ///   opens on `(`.
    /// - ensures: each parameter binds in a frame extending the one before it,
    ///   left to right, with its type, when written, read as a value type under
    ///   the frame before it and recorded on the binder; a recursive tail
    ///   stages the parameter `Native::staged_by_body` reads off its body and
    ///   binds its own name in one more frame, between that parameter and the
    ///   ones before it — after its empty list when it has none — typed by the
    ///   declaration form so no telescope counts it, records the parameters
    ///   before it as the ones every recursive call passes unchanged, and
    ///   records each parameter's position as the one a match on it
    ///   scrutinises; the result, when written, is read at the result position
    ///   under the last parameter's frame, as the block is, and recorded as the
    ///   answer of the block's last computation and of every statement whose
    ///   local ends continue the block; the block, or the one expression after
    ///   `=` read as a block of no statement, is read as a body a path runs
    ///   through; the form is planned as the function's declared type and body.
    /// - provides: the function tail, lowered once at the declaration form for
    ///   both halves it writes.
    /// - fails: yields the unadmitted refusal for a parameter spelled as a type
    ///   or a type variable; a fault naming the function form for a parameter
    ///   list, a type or a result out of shape; a form fault reading a
    ///   recursive tail's body ahead; the block's own refusal; and the
    ///   unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The function's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameter count is separated by none and two,
    ///   each lowered tail asserted as the exact core node read back out of the
    ///   arena, a recursive tail of none binding its own name, and the refusals
    ///   by a type-spelled parameter and a juxtaposed parameter type, each
    ///   asserted as the exact variant.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `gandr-surface-lowering::lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_juxtaposed_operand_is_refused`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterless_recursive_tail_binds_its_own_name_1499`
    #[spec(
        captures: parameters = self.cx().parameters.mark(),
        ensures: |ret| {
            ret.is_err()
                || self
                    .cx().plans
                    .get(site.at.node)
                    .is_some_and(|plan| match *plan {
                        | Plan::Function(ref function) => {
                            function.parameters == self.cx().parameters.since(parameters)
                                && match function.body {
                                    | Body::Block(block) => self.cx().statements.whole(block.statements).is_some(),
                                    | Body::Clauses(_) => true,
                                }
                        },
                        | _ => false,
                    })
        },
    )]
    fn function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let function = Site {
            name: FormName::FUNCTION,
            ..site
        };
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::DEF => break,
                Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
                Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
        let recursive = cursor.tile(TileName::REC);
        let named = cursor.tile(TileName::IDENTIFIER);
        self.shared().merge_refusal(site.at.node)?;
        self.stage_telescope(site, &mut cursor)?;
        // A clause tail of no written parameter, `: T where { … }`, opens on
        // its type's `:`.
        let listing = cursor.tile(TileName::PAREN_OPEN);
        if let (Maybe::Absent(_), Maybe::Absent(_)) = (listing, cursor.at(TileName::COLON)) {
            return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
        }
        let receiver = CapabilityRef::new(self.host_ref()).receiver_mode(site);
        CapabilityRef::new(self.host_ref()).stray_modes(&cursor, receiver)?;
        let start = self.cx().parameters.mark();
        // The mode variable a deduced receiver is written at, `self : m T`.
        let mut deduced: Option<SurfaceName<'source>> = None;
        // A recursive tail stages the parameter its body's matches take
        // apart, read off the syntax ahead before anything binds: the written
        // list, which the calls' arguments follow, then counted over a merged
        // telescope's parameters. A parameter whose type is a decode carries
        // no stage (`Self::decodes`).
        let staged = match (recursive, named) {
            (Maybe::Present(_), Maybe::Present(own)) => {
                let mut ahead = cursor.clone();
                let mut names = Vec::new();
                let mut types: Vec<Option<NodeIndex>> = Vec::new();
                let mut roots = Vec::new();
                let mut listed = matches!(listing, Maybe::Present(_));
                // A clause tail states its type after the list, or after the
                // name when it writes none: the first tile there is `:`.
                let mut first = !listed;
                let mut clausal = false;
                // Where the parameter being read starts: names that share a
                // type, `m n : T`, each take it.
                let mut group = 0_usize;
                while let Maybe::Present(piece) = ahead.read() {
                    match piece {
                        Piece::Tile { label, .. } if first => {
                            clausal = label == TileName::COLON;
                            first = false;
                        },
                        Piece::Tile { label, at }
                            if listed && TileName::BINDERS.contains(&label) =>
                        {
                            names.push(self.cx().name_at(at));
                            types.push(None);
                        },
                        Piece::Tile { label, .. } if label == TileName::PAREN_CLOSE && listed => {
                            listed = false;
                            first = true;
                        },
                        Piece::Tile { label, .. } if label == TileName::COMMA && listed => {
                            group = types.len();
                        },
                        Piece::Operand(operand) if listed => {
                            for typed in types.iter_mut().skip(group) {
                                *typed = Some(operand.node);
                            }
                        },
                        Piece::Operand(operand) => roots.push(operand.node),
                        Piece::Tile { .. } => {},
                    }
                }
                let mut decoded = Vec::with_capacity(types.len());
                for ty in types {
                    decoded.push(match ty {
                        Some(ty) => Native::new(self.host()).decodes(site, Frame::Outermost, ty)?,
                        None => native::Decoded(false),
                    });
                }
                let own = self.cx().name_at(own);
                let joint = match self.cx().collected.owner_of(site.at.node) {
                    Maybe::Present(owner) => NativeRef::over(self.cx()).joint(owner),
                    Maybe::Absent(_) => native::Joint::alone(),
                };
                // Clauses stage the column their tree first switches on,
                // which `Self::clauses` records once the tree is compiled;
                // every written parameter stays outside the fixpoint.
                let written = if clausal {
                    native::Staging {
                        kept: native::ParameterAt(names.len()),
                        staged: native::ParameterAt(names.len()),
                    }
                }
                else {
                    Native::new(self.host())
                        .staged_by_body(own, &joint, &names, &decoded, &roots)?
                };
                Some(self.merged_staging(site, written)?)
            },
            _ => None,
        };
        let mut own = OwnName {
            pending: match (named, staged) {
                (Maybe::Present(named), Some(staging)) => Some((named, staging, start)),
                _ => None,
            },
            bound: Maybe::Absent(recursion::Absent::Plain),
        };
        let mut frame =
            self.merged_parameters(site, function, &mut cursor, Frame::Outermost, &mut own)?;
        // The written parameters at a session type.
        let mut endpoints = Vec::new();
        loop {
            let first = match cursor.peek() {
                _ if matches!(listing, Maybe::Absent(_)) => break,
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    let _close = cursor.tile(TileName::PAREN_CLOSE);
                    break;
                },
                Maybe::Present(Piece::Tile { label, at }) if TileName::BINDERS.contains(&label) => {
                    let _binder = cursor.tile(label);
                    at
                },
                Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            };
            // Names that share a type, `m n : T`, each bind it in turn.
            let shared = cursor.shared(&TileName::BINDERS);
            let mut endpoint = session::Stands::Other;
            let declared = match cursor.tile(TileName::COLON) {
                Maybe::Present(_) => {
                    // A receiver's mode word, which the collection read.
                    if let Maybe::Absent(_) = cursor.tile(TileName::SHARED) {
                        let _consumed = cursor.tile(TileName::CONSUMED);
                    }
                    let mut declared = function.one(cursor.operands())?;
                    // A receiver at a mode variable, `self : m T`: the variable
                    // names a mode binder, and `T` is the receiver's type.
                    if let Some((mode, typed)) =
                        CapabilityRef::new(self.host_ref()).moded(declared)?
                    {
                        deduced =
                            Some(CapabilityRef::new(self.host_ref()).mode_variable(site, mode)?);
                        declared = typed;
                    }
                    // A parameter at a session type, written or named, is an
                    // endpoint its body places.
                    endpoint = Capability::new(self.host()).stands(declared, frame)?;
                    self.read(declared.node, Reading::ValueType(frame));
                    Maybe::Present(declared.node)
                },
                Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
            };
            // Only a stated type is shared: `(m n)` states none.
            if let Some(second) = shared.clone().next()
                && let Maybe::Absent(_) = declared
            {
                return Err(function.fault(second.span, FormFault::MisplacedTile));
            }
            for binder in core::iter::once(first).chain(shared) {
                let name = self.cx().name_at(binder);
                self.note_binder(binder, frame, name)?;
                frame = self.bind_kept(site, &mut own, frame);
                let written = Maybe::Present(binder.span);
                let bound = match declared {
                    Maybe::Present(declared) => self
                        .cx_mut()
                        .scope
                        .extend_typed(frame, name, declared, written),
                    Maybe::Absent(_) => self.cx_mut().scope.extend(frame, name, written),
                };
                let parameter = Parameter::own(binder.node, bound, declared);
                if endpoint == session::Stands::Session {
                    endpoints.push(parameter);
                }
                self.cx_mut().parameters.push(parameter);
                frame = Frame::Inner(bound);
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        // A tail that keeps every parameter binds its own name after its
        // list: the loop above met no parameter to bind it before.
        frame = self.bind_kept(site, &mut own, frame);
        // A clause tail binds one more parameter per column of its stated
        // type, after its own name.
        let columns = match cursor.at(TileName::COLON) {
            Maybe::Present(_) => {
                Some(Native::new(self.host()).columns(function, &mut cursor, frame)?)
            },
            Maybe::Absent(_) => None,
        };
        let recursion = own.bound;
        let parameters = self.cx().parameters.since(start);
        if let Maybe::Present(own) = recursion
            && let Some(held) = self.cx_mut().recursions.get_mut(&own)
        {
            held.parameters = parameters;
            let cx = self.cx_mut();
            for (position, parameter) in cx.parameters.read(parameters).iter().enumerate() {
                let scrutiny = native::Scrutiny {
                    recursion: own,
                    position: native::ParameterAt(position),
                };
                let _first = cx.staged_parameters.insert(parameter.frame, scrutiny);
            }
        }
        if let Some(columns) = columns {
            if deduced.is_some() {
                return Err(LoweringRefusal::ViewNotPlace {
                    span: function.at.span,
                });
            }
            if receiver == Some(ReceiverMode::Exclusive) {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
            let case = Native::new(self.host()).clauses(
                function,
                &mut cursor,
                frame,
                &columns,
                recursion,
            )?;
            self.plan(
                site,
                Plan::Function(Function {
                    parameters,
                    result: Maybe::Present(columns.result),
                    body: Body::Clauses(case),
                    recursion,
                    receiver: Maybe::Absent(method::unheld::Absent::NotWrittenThrough),
                    endpoints: FormStretch::default(),
                    taking: Taking::Unrestricted,
                }),
            );
            return Ok(());
        }
        let arrow = match cursor.tile(TileName::ARROW) {
            Maybe::Present(_) => Some(Taking::Unrestricted),
            Maybe::Absent(_) => match cursor.tile(TileName::LINEAR_ARROW) {
                Maybe::Present(_) => Some(Taking::Linear),
                Maybe::Absent(_) => None,
            },
        };
        let (result, viewed, taking) = match arrow {
            Some(taking) => {
                // A linear parameter's shadow binds in the arrow's codomain
                // whether or not the result names it, so every telescope
                // counts its frame.
                if taking == Taking::Linear {
                    let cx = self.cx_mut();
                    for parameter in cx.parameters.read(parameters) {
                        if parameter.listed == Listed::Own {
                            cx.scope.mention(parameter.frame);
                        }
                    }
                }
                let result = function.one(cursor.operands())?;
                let viewed = match deduced {
                    Some(mode) => {
                        Some(Capability::new(self.host()).view_result(result, mode, frame)?)
                    },
                    None => None,
                };
                self.read(result.node, Reading::Result(frame));
                (Maybe::Present(result.node), viewed, taking)
            },
            None if deduced.is_some() => {
                return Err(LoweringRefusal::ViewNotPlace {
                    span: function.at.span,
                });
            },
            None => (
                Maybe::Absent(stated::Absent::Unstated),
                None,
                Taking::Unrestricted,
            ),
        };
        let (placed, endpoints) = Capability::new(self.host()).place_endpoints(frame, &endpoints);
        let (body, receiver) = match receiver {
            Some(ReceiverMode::Exclusive) => {
                let (held, receiver) =
                    Capability::new(self.host()).hold_receiver(function, placed, parameters)?;
                (held, Maybe::Present(receiver))
            },
            Some(ReceiverMode::Shared | ReceiverMode::Consumed | ReceiverMode::Deduced) | None => (
                placed,
                Maybe::Absent(method::unheld::Absent::NotWrittenThrough),
            ),
        };
        let block = if let Maybe::Present(_) = cursor.at(TileName::EQUALS) {
            self.expression_body(function, &mut cursor, body)?
        }
        else {
            self.block(function, &mut cursor, body)?
        };
        if let Some(element) = viewed {
            Capability::new(self.host()).view_body(function, block, element)?;
        }
        let answer = match result {
            Maybe::Present(node) => {
                let answer = native::Answer {
                    node,
                    frame,
                    over: native::Over::Written,
                    arm: Maybe::Absent(native::passed::Absent::Unpassed),
                };
                let _first = self.cx_mut().answers.insert(block.last, answer);
                Maybe::Present(answer)
            },
            Maybe::Absent(_) => Maybe::Absent(native::answered::Absent::Unstated),
        };
        Exits::new(self.host()).open_body(function, block, answer)?;

        self.plan(
            site,
            Plan::Function(Function {
                parameters,
                result,
                body: Body::Block(block),
                recursion,
                receiver,
                endpoints,
                taking,
            }),
        );

        Ok(())
    }

    /// Bind a recursive tail's own name, written at `own`, in one more frame
    /// over `frame`, and record its fixpoint: the parameters `uniform` every
    /// recursive call passes unchanged, and the one at `staged` it stages.
    ///
    /// # Specification
    /// - requires: `site` is the declaration form the tail writes; `uniform` is
    ///   the parameters the tail read before its own name, ending at the
    ///   store's end.
    /// - ensures: the frame binds `own`'s name over `frame`, typed by the
    ///   declaration form so no telescope counts it, and keys the tail's
    ///   recursion, unclaimed, its parameters not yet read.
    /// - provides: the one binding of a recursive tail's name, before the
    ///   parameter after the kept ones or, for a tail of none, after its empty
    ///   list.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::function`].
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterless_recursive_tail_binds_its_own_name_1499`
    #[spec(
        ensures: |ret| self.cx().recursions.get(&ret).is_some_and(|held| held.uniform == uniform
            && held.staged == staged
            && held.parameters == FormStretch::default()),
    )]
    fn bind_own(
        &mut self,
        site: Site,
        own: Placed,
        frame: Frame,
        uniform: FormStretch,
        staged: native::ParameterAt,
    ) -> ScopeId
    {
        let named = own.node;
        let name = self.cx().name_at(own);
        let bound =
            self.cx_mut()
                .scope
                .extend_typed(frame, name, site.at.node, Maybe::Present(own.span));
        let _first = self.cx_mut().recursions.insert(bound, native::Recursion {
            parameters: FormStretch::default(),
            uniform,
            staged,
            claimed: native::Claimed(false),
            named,
        });

        bound
    }

    /// Bind a recursive tail's own name over `frame` once the parameter store
    /// holds exactly the parameters every recursive call keeps.
    ///
    /// # Specification
    /// - requires: `own` is the tail's own name, read before its parameters
    ///   bind; `site` is the declaration form the tail writes.
    /// - ensures: when `own` is pending and the store holds its kept count of
    ///   parameters past its start, the name binds over `frame`
    ///   ([`Self::bind_own`]), `own` holds the binding and its frame is
    ///   returned; otherwise nothing changes and `frame` is returned.
    /// - provides: the one check both parameter lists — the written one and a
    ///   merged telescope's — read the own name's place by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::function`]; a tail under a row that names
    ///   an instance binds its own name before its first parameter.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterless_recursive_tail_binds_its_own_name_1499`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursion_under_an_instance_row_binds_its_own_name_3699`
    #[spec(ensures: |ret| own.pending.is_none() || ret == frame)]
    fn bind_kept(
        &mut self,
        site: Site,
        own: &mut OwnName,
        frame: Frame,
    ) -> Frame
    {
        let Some((named, staging, start)) = own.pending
        else {
            return frame;
        };
        if usize::from(self.cx().parameters.mark()).saturating_sub(usize::from(start))
            != staging.kept.0
        {
            return frame;
        }
        let uniform = self.cx().parameters.since(start);
        let bound = self.bind_own(site, named, frame, uniform, staging.staged);
        own.pending = None;
        own.bound = Maybe::Present(bound);

        Frame::Inner(bound)
    }

    /// Read a block, `{ s… c }`, whose first statement reads under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the block's `{`, which the form's last
    ///   piece closes.
    /// - ensures: each `let x = c ;` statement reads its computation under the
    ///   frame the statements before it extended and binds `x` in a frame
    ///   extending that one; `let x = recv c;` binds `x` the same way, and
    ///   `fork (c : S) t as d ;` binds `d` and `var x = e ;` binds `x` linearly
    ///   over the rest of the block; the last computation, written bare or as a
    ///   statement `c ;` before the closing `}` and then recorded as stated,
    ///   reads under the frame every statement extended; a block-like form (a
    ///   block, a loop, an `if`, a `match`, or a form closing on a block)
    ///   followed by another statement is a statement with no `;`, its result
    ///   discarded, as Rust reads one; the statements and the last computation
    ///   are returned, with the cursor past the closing `}` and nothing after
    ///   it.
    /// - provides: the body reading of thunks, lambdas and function tails.
    /// - fails: yields the unadmitted or the reserved refusal for a statement
    ///   the fragment does not read, by the statement's own name; the arity
    ///   refusal, as a block, for a block with no last computation; and each
    ///   statement's and hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the statement count is separated by none and two, the
    ///   second binding over the first, each asserted as the exact bind chain
    ///   read back out of the arena; the residue by one witness row per refused
    ///   statement form, asserted as the exact refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `gandr-surface-lowering::lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `gandr-surface-lowering::lower::session::tests::a_fork_in_a_joined_arm_leaves_the_rest_its_own_slots_1500`
    /// - witness: `gandr-surface-lowering::lower::access::tests::a_hold_in_a_joined_arm_leaves_the_rest_its_own_slots_1500`
    /// - witness: `gandr-surface-lowering::lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_like_statement_needs_no_semicolon`
    #[spec(
        captures: before = (self.cx().statements.mark(), frame),
        ensures: |ret| {
            ret.as_ref().map_or(true, |block| {
                block.statements == self.cx().statements.since(before.0)
                    && matches!(self.cx().reading(block.last), Reading::Computation(_))
                    && (!self.cx().statements.read(block.statements).is_empty()
                        || self.cx().reading(block.last) == Reading::Computation(before.1))
                    && matches!(cursor.peek(), Maybe::Absent(_))
            })
        },
    )]
    #[inline]
    pub fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        let Maybe::Present(open) = cursor.tile(TileName::BRACE_OPEN)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let start = self.cx().statements.mark();
        let mut frame = frame;
        loop {
            match cursor.peek() {
                Maybe::Present(Piece::Operand(first)) => {
                    if self.shared().ends_a_statement(first, cursor)?.0 {
                        let _first = cursor.read();
                        frame = self.discard(site, first, frame)?;
                        continue;
                    }
                    let mut run = cursor.operands();
                    if let Maybe::Present(Piece::Tile { label, .. }) = cursor.peek()
                        && access::ASSIGNING.contains(&label)
                    {
                        run = Run::One(
                            Capability::new(self.host()).assignment(site, cursor, run, frame)?,
                        );
                    }
                    if let Maybe::Present(semicolon) = cursor.at(TileName::SEMICOLON) {
                        let first = match run {
                            Run::One(written) | Run::Several { first: written, .. } => written.span,
                            Run::Empty(gap) => gap,
                        };
                        let span = first.join(semicolon.span);
                        let mut ahead = cursor.clone();
                        let _semicolon = ahead.tile(TileName::SEMICOLON);
                        if let (Run::One(written), Maybe::Present(_)) =
                            (run, ahead.at(TileName::BRACE_CLOSE))
                        {
                            let _semicolon = cursor.tile(TileName::SEMICOLON);
                            let _first = self.cx_mut().stated.insert(written.node, span);
                            closed(site, cursor, TileName::BRACE_CLOSE)?;
                            exhausted(site, cursor)?;
                            let _rest = Exits::new(self.host()).threads(
                                site,
                                written.node,
                                (frame, frame),
                            )?;
                            self.read(written.node, Reading::Computation(frame));
                            return Ok(Block {
                                statements: self.cx().statements.since(start),
                                last: written.node,
                            });
                        }
                        let discarded = site.one(run)?;
                        let _semicolon = cursor.tile(TileName::SEMICOLON);
                        frame = self.discard(site, discarded, frame)?;
                        continue;
                    }
                    let last = site.one(run)?;
                    closed(site, cursor, TileName::BRACE_CLOSE)?;
                    exhausted(site, cursor)?;
                    let _rest = Exits::new(self.host()).threads(site, last.node, (frame, frame))?;
                    self.read(last.node, Reading::Computation(frame));
                    return Ok(Block {
                        statements: self.cx().statements.since(start),
                        last: last.node,
                    });
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    let braced = ByteSpan::new(open.span.start(), site.at.span.end())
                        .unwrap_or(site.at.span);
                    let as_block = Site {
                        at: Placed {
                            node: site.at.node,
                            span: braced,
                        },
                        name: FormName::BLOCK,
                        reading: Reading::Computation(frame),
                    };
                    return Err(as_block.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
                },
                Maybe::Present(Piece::Tile { label, at }) => {
                    if !STATEMENT_KEYWORDS.contains(&label) {
                        return Err(site.fault(at.span, FormFault::MisplacedTile));
                    }
                    let _keyword = cursor.read();
                    frame = if label == TileName::LET || label == TileName::MODULE {
                        let after = if label == TileName::LET {
                            self.let_statement(cursor, at, frame)?
                        }
                        else {
                            Models::new(self.host()).module_statement(cursor, at, frame)?
                        };
                        match self.cx().statements.last() {
                            Some(&Statement { bound, .. }) => {
                                Exits::new(self.host()).threads(site, bound, (frame, after))?
                            },
                            None => after,
                        }
                    }
                    else if label == TileName::VAR {
                        Capability::new(self.host()).hold(cursor, at, frame)?
                    }
                    else {
                        self.open(site, cursor, at)?;
                        frame
                    };
                },
                Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
    }

    /// Read a function's body written as one expression after `=`, `= e ;`:
    /// the block of no statement whose last computation is `e`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the body's `=`, which the form's last
    ///   piece, `;`, closes.
    /// - ensures: `e` is read as a computation under `frame`, as a block's last
    ///   computation is, and returned as the block's last over no statement,
    ///   with the cursor past the `;` and nothing after it.
    /// - fails: the form's fault for a missing or several expressions, a
    ///   missing `;`, or anything after it.
    /// - panics: none.
    ///
    /// # Errors
    /// The body's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body after `=` lowers as the braced block of its
    ///   one expression does.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_body_after_equals_is_its_block_4853`
    #[spec(
        captures: before = frame,
        ensures: |ret| {
            ret.as_ref().map_or(true, |block| {
                block.statements == FormStretch::default()
                    && self.cx().reading(block.last) == Reading::Computation(before)
                    && matches!(cursor.peek(), Maybe::Absent(_))
            })
        },
    )]
    fn expression_body(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        let Maybe::Present(_) = cursor.tile(TileName::EQUALS)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let last = site.one(cursor.operands())?;
        closed(site, cursor, TileName::SEMICOLON)?;
        exhausted(site, cursor)?;
        let _rest = Exits::new(self.host()).threads(site, last.node, (frame, frame))?;
        self.read(last.node, Reading::Computation(frame));

        Ok(Block {
            statements: FormStretch::default(),
            last: last.node,
        })
    }

    /// Record the computation `discarded` as a statement of the block `site`
    /// reads, standing under `frame`, its result discarded.
    ///
    /// # Specification
    /// - requires: `discarded` is a computation of the block, its cursor past
    ///   it and past the `;` after it when one is written.
    /// - ensures: `discarded` is read as a computation under `frame` and
    ///   recorded as a discarded statement; the frame the rest of the block
    ///   reads under, extended by a binder no name reaches and by the slots a
    ///   loop threads, is returned.
    /// - fails: as [`Exits::threads`].
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement written with `;` and a block-like one
    ///   written without it each bind under a binder no name reaches.
    /// - witness: `gandr-surface-lowering::lower::tests::a_discarded_statement_splits_its_unit`
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_like_statement_needs_no_semicolon`
    #[spec(
        captures: before = self.cx().statements.mark(),
        ensures: |ret| ret.is_err() || (self.cx().statements.mark() == before.next()
            && self.cx().statements.last().is_some_and(|last| last.bound == discarded.node && last.binding == StatementBinding::Discarded)),
    )]
    fn discard(
        &mut self,
        site: Site,
        discarded: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        self.read(discarded.node, Reading::Computation(frame));
        self.cx_mut().statements.push(Statement {
            origin: discarded.node,
            bound: discarded.node,
            binding: StatementBinding::Discarded,
            rest: exits::Rest::Bound,
        });
        let after = Frame::Inner(self.cx_mut().scope.extend(
            frame,
            SurfaceName::from(""),
            Maybe::Absent(binder_site::Absent::Unwritten),
        ));
        Exits::new(self.host()).threads(site, discarded.node, (frame, after))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Whether the operand `first`, at the head of `cursor`, is a block-like
    /// form another statement follows with no `;` between: a block, a loop,
    /// an `if`, a `match`, or an access or a handled scope closing on its
    /// block.
    ///
    /// # Specification
    /// - requires: `cursor` stands at `first`.
    /// - ensures: true exactly when `first` is such a form and the piece after
    ///   it is an operand or a tile other than `;`, `}` and an assignment's;
    ///   the cursor is left where it stands.
    /// - fails: a fault reading the form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `while` and an `if` before a statement, a `while`
    ///   before the block's last computation, and one before `;`.
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_like_statement_needs_no_semicolon`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |ends| !ends.0 || matches!(cursor.peek(), Maybe::Present(Piece::Operand(at)) if at == first)))]
    fn ends_a_statement(
        &self,
        first: Placed,
        cursor: &Cursor<'_>,
    ) -> Result<Ends, LoweringRefusal<'source>>
    {
        let mut ahead = cursor.clone();
        let _first = ahead.read();
        let followed = match ahead.peek() {
            Maybe::Present(Piece::Operand(_)) => true,
            Maybe::Present(Piece::Tile { label, .. }) => {
                label != TileName::SEMICOLON
                    && label != TileName::BRACE_CLOSE
                    && !access::ASSIGNING.contains(&label)
            },
            Maybe::Absent(_) => false,
        };
        if !followed {
            return Ok(Ends(false));
        }
        let block_like = match self.cx().form_at(first)? {
            Some((
                _,
                Former::Block
                | Former::Loop
                | Former::While
                | Former::For
                | Former::If
                | Former::Case,
            )) => true,
            Some((_, Former::Access | Former::Scope)) => {
                let mut pieces = Pieces::new();
                read_pieces(self.cx().pbg, self.cx().tree, first.node, &mut pieces)?;
                matches!(pieces.pieces.last(), Some(&Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE)
            },
            Some(_) | None => false,
        };

        Ok(Ends(block_like))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Bind what the computation `bound` returns to `binder`, the `let`
    /// statement at `statement` having read its parts, when its binder is a
    /// pattern other than a name, its name binds a buffer an exercise places,
    /// or `bound` is a computation that only runs.
    ///
    /// # Specification
    /// - requires: `binder`, `annotation` and `bound` are the statement's
    ///   pattern, its stated type and its bound computation; `frame` is the
    ///   frame the statement reads under.
    /// - ensures: the statement's computation is read under `frame` and the
    ///   statement recorded with the tile at `statement`; the frame binding the
    ///   statement's names over `frame`, which the rest of the block reads
    ///   under, is returned. A tuple pattern `(x, y, …)` of a call whose result
    ///   is a group of as many outputs, as `Models::called_outputs` reads it,
    ///   binds each output to its component's name, in order, and the statement
    ///   is recorded as that bind of outputs; any other tuple pattern binds the
    ///   returned tuple under a nameless binder and each component's name over
    ///   it, in order, and the statement is recorded as that split. pattern
    ///   annotated `: A` reads `A` in `frame` and binds over it, and the
    ///   statement is recorded as the bind of `c` ascribed `-F A`. A name
    ///   written with no type is recorded with `frame` and `c`, which
    ///   `Models::ran_type` reads its type off.
    /// - fails: yields the unadmitted refusal for a binder pattern other than a
    ///   name, a wildcard or a tuple of those, and a fault naming the statement
    ///   for a hole or a tile out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each such statement reads its bound computation in
    ///   the previous frame and introduces its names only for subsequent
    ///   computations; a two-component tuple binds both names in order, so a
    ///   swapped binding reads the other component; an annotated tuple checks
    ///   the bound computation against its type before binding.
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `gandr-surface-lowering::lower::tests::a_let_binds_a_value_once_and_a_computation_nested`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    /// - witness: `gandr-surface-lowering::lower::tests::a_typed_tuple_binder_ascribes_and_splits_1543`
    #[spec(
        captures: before = self.cx().statements.mark(),
        ensures: |ret| match ret {
            | Ok(Frame::Inner(_)) => {
                self.cx().statements.mark() == before.next()
                    && self.cx().statements.last().is_some_and(|last| {
                        last.origin == statement.at.node
                            && matches!(last.binding, StatementBinding::Named(_) | StatementBinding::Placed(_) | StatementBinding::Split { .. } | StatementBinding::Outputs { .. } | StatementBinding::Typed { .. } | StatementBinding::TypedSplit { .. })
                            && self.cx().reading(last.bound) == Reading::Computation(frame)
                    })
            },
            | Ok(Frame::Outermost) => false,
            | Err(_) => self.cx().statements.mark() == before,
        },
    )]
    fn bound_statement(
        &mut self,
        statement: Site,
        (binder, annotation, bound): (Placed, Option<Placed>, Placed),
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let run = statement.at;
        if let Maybe::Present(components) = self.shared().tuple_binders(statement, binder)? {
            let mut names = Vec::with_capacity(components.len());
            for &(label, component) in &components {
                // A punned `.l` binds its own label.
                let name = if label == Some(component) {
                    self.cx().name_at(component)
                }
                else {
                    self.shared().binder_name(statement, component)?
                };
                self.note_binder(component, frame, name)?;
                names.push((
                    label.map(|label| (self.cx().name_at(label), label)),
                    name,
                    component,
                ));
            }
            let pattern = Site {
                at: binder,
                name: FormName::TUPLE_PATTERN,
                reading: Reading::Computation(frame),
            };
            // The grammar holds a group all positional or all labelled.
            let labelled = names.iter().filter(|&&(label, ..)| label.is_some()).count();
            self.read(bound.node, Reading::Computation(frame));
            let arity = gandr_core_term::ComponentCount::from(names.len());
            let outputs = match annotation {
                None => Models::new(self.host()).called_outputs(frame, bound, run.node)?,
                Some(_) => None,
            };
            // A pattern of a call returning outputs binds every one of them.
            if outputs
                .as_ref()
                .is_some_and(|outputs| outputs.len() != names.len())
            {
                return Err(pattern.out(FragmentBoundary::Arity(OperandCount::from(names.len()))));
            }
            if let Some(outputs) = outputs {
                // A labelled pattern binds each output by its label, in the
                // order the callee writes them.
                let ordered: Vec<(SurfaceName<'source>, Placed)> = if labelled == 0 {
                    names
                        .iter()
                        .map(|&(_, name, component)| (name, component))
                        .collect()
                }
                else {
                    let called: Vec<SurfaceName<'source>> = outputs
                        .iter()
                        .filter_map(|output| match output.key {
                            arity::Key::Label(written, _) => Some(written),
                            arity::Key::Positional | arity::Key::Index(..) => None,
                        })
                        .collect();
                    // Labels name the outputs of a callee that names each.
                    if called.len() != outputs.len() {
                        return Err(pattern.out(FragmentBoundary::WrongSort));
                    }
                    let callable: BTreeSet<SurfaceName<'source>> = called.iter().copied().collect();
                    let mut ordered = Vec::with_capacity(names.len());
                    // Each label's key, and the name and the binder it binds.
                    let mut seen: BTreeMap<
                        SurfaceName<'source>,
                        (Placed, SurfaceName<'source>, Placed),
                    > = BTreeMap::new();
                    for &(label, name, component) in &names {
                        let Some((written, key)) = label
                        else {
                            continue;
                        };
                        if !callable.contains(&written) {
                            return Err(statement.fault(key.span, FormFault::MisplacedTile));
                        }
                        if let Some(&(first, ..)) = seen.get(&written) {
                            return Err(LoweringRefusal::DuplicateDefinition {
                                span: key.span,
                                name: written,
                                first: first.span,
                            });
                        }
                        seen.insert(written, (key, name, component));
                    }
                    for written in called {
                        if let Some(&(_, name, component)) = seen.get(&written) {
                            ordered.push((name, component));
                        }
                    }
                    ordered
                };
                self.cx_mut().statements.push(Statement {
                    origin: run.node,
                    bound: bound.node,
                    binding: StatementBinding::Outputs {
                        arity,
                        pattern: binder.node,
                    },
                    rest: exits::Rest::Bound,
                });
                // Each output's binder answers where its pattern writes it,
                // a binder nothing reads included.
                let _first = self.cx_mut().output_binders.insert(
                    binder.node,
                    ordered
                        .iter()
                        .map(|&(_, component)| component.node)
                        .collect(),
                );
                let mut inner = frame;
                for (name, written) in ordered {
                    inner = Frame::Inner(self.cx_mut().scope.extend(
                        inner,
                        name,
                        Maybe::Present(written.span),
                    ));
                }
                return Ok(inner);
            }
            // Labels name the outputs of a call. A `#{ … }` pattern matches a
            // record value.
            if labelled != 0 {
                return Err(pattern.out(FragmentBoundary::WrongSort));
            }
            let names: Vec<_> = names
                .into_iter()
                .map(|(_label, name, written)| (name, written.span))
                .collect();
            let binding = annotation.map_or_else(
                || StatementBinding::Split {
                    arity,
                    pattern: binder.node,
                },
                |annotation| {
                    self.read(annotation.node, Reading::ValueType(frame));
                    StatementBinding::TypedSplit {
                        arity,
                        pattern: binder.node,
                        annotation: annotation.node,
                    }
                },
            );
            self.cx_mut().statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding,
                rest: exits::Rest::Bound,
            });
            let mut inner = self.cx_mut().scope.extend(
                frame,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            );
            for (name, written) in names {
                inner =
                    self.cx_mut()
                        .scope
                        .extend(Frame::Inner(inner), name, Maybe::Present(written));
            }
            return Ok(Frame::Inner(inner));
        }
        let name = self.shared().binder_name(statement, binder)?;
        self.note_binder(binder, frame, name)?;
        if let Some(annotation) = annotation {
            self.read(bound.node, Reading::Computation(frame));
            self.read(annotation.node, Reading::ValueType(frame));
            self.cx_mut().statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding: StatementBinding::Typed {
                    name: binder.node,
                    annotation: annotation.node,
                },
                rest: exits::Rest::Bound,
            });
            return Ok(Frame::Inner(self.cx_mut().scope.extend(
                frame,
                name,
                Maybe::Present(binder.span),
            )));
        }
        if Capability::new(self.host()).placing(statement, frame, bound)?
            == capability::Reply::Minted
        {
            self.read(bound.node, Reading::Computation(frame));
            self.cx_mut().statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding: StatementBinding::Placed(binder.node),
                rest: exits::Rest::Bound,
            });
            let reply = self.cx_mut().scope.extend(
                frame,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            );
            return Ok(Frame::Inner(self.cx_mut().scope.extend_linear(
                Frame::Inner(reply),
                name,
                Maybe::Present(binder.span),
            )));
        }
        self.read(bound.node, Reading::Computation(frame));
        self.cx_mut().statements.push(Statement {
            origin: run.node,
            bound: bound.node,
            binding: StatementBinding::Named(binder.node),
            rest: exits::Rest::Bound,
        });
        let bound_at = self
            .cx_mut()
            .scope
            .extend(frame, name, Maybe::Present(binder.span));
        let _first = self.cx_mut().ran.insert(bound_at, (frame, bound));

        Ok(Frame::Inner(bound_at))
    }

    /// Read one `let p = e ;` or `let p : A = e ;` statement, its `let` tile
    /// already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's `let` tile `lead`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: a receive or a fork `e` is read as [`Capability::receive`]
    ///   and [`Capability::fork`] read it, binding the name the pattern spells.
    ///   A name under `at` with no stated type, `let x at w = e ;`, opens the
    ///   handle `e` at `w` as [`Self::opened`] reads it. A block, a match, a
    ///   conditional, a loop, an exit, a loop exit, a scope, an access, an
    ///   offer, an action, a hold or a migration `e` binds what it returns, as
    ///   [`Self::bound_statement`] binds it. Otherwise a name binder reads `e`
    ///   as a value under `frame`, a computation there nested at
    ///   [`Insertion::Bound`], and `A` as a value type when written; the
    ///   statement is recorded as a `let` of `e`, and the frame binding the
    ///   name over `frame` returned, at `A` when written, so a member reads off
    ///   it as off a parameter of that type; a binder the mint binds once to
    ///   what `e` returns. The checker runs a nested call that returns and
    ///   suspends any other. Any other pattern, and a name over an exercise
    ///   that places a buffer, binds what `e` returns, as
    ///   [`Self::bound_statement`] binds it, a value `e` returned.
    /// - fails: a fault naming the let statement for a hole or a tile out of
    ///   shape, or for a type stated over a receive or a fork; the binder's and
    ///   the bound computation's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value bound to a name is returned once and read
    ///   through the binder, and a call bound to a name is nested once, at the
    ///   bound insertion; a member reads off a binder stated at a model type.
    /// - witness: `gandr-surface-lowering::lower::tests::a_let_binds_a_value_once_and_a_computation_nested`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_member_reads_off_a_let_binder_at_a_model_type_4827`
    #[spec(
        captures: before = self.cx().statements.mark(),
        ensures: |ret| ret.is_err() || (self.cx().statements.mark() == before.next()
            && self.cx().statements.last().is_some_and(|last| last.origin == lead.node)),
    )]
    #[inline]
    pub fn let_statement(
        &mut self,
        cursor: &mut Cursor<'_>,
        lead: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: lead,
            name: FormName::LET_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let binder = statement.one(cursor.operands())?;
        let annotation = if let Maybe::Present(_colon) = cursor.tile(TileName::COLON) {
            Some(statement.one(cursor.operands())?)
        }
        else {
            None
        };
        closed(statement, cursor, TileName::EQUALS)?;
        let bound = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        // A receive and a fork each give one linear end, which the pattern
        // names.
        if let Some((form, _former)) = self.cx().form_at(bound)?
            && (form == FormName::RECV_EXPRESSION || form == FormName::FORK_EXPRESSION)
        {
            if let Some(annotation) = annotation {
                return Err(statement.fault(annotation.span, FormFault::MisplacedTile));
            }
            let name = self.shared().binder_name(statement, binder)?;
            return if form == FormName::RECV_EXPRESSION {
                Capability::new(self.host()).receive(statement, (binder, name), bound, frame)
            }
            else {
                Capability::new(self.host()).fork(statement, (binder, name), bound, frame)
            };
        }
        // A name under `at` opens the handle `e` at the world written.
        if annotation.is_none()
            && let Some((_, Former::AtType)) = self.cx().form_at(binder)?
            && let Maybe::Present(after) = self.opened(statement, binder, bound, frame)?
        {
            return Ok(after);
        }
        // A name stands for the value `e` is read as: a call there nests,
        // which the checker runs or suspends where the statement stands. A
        // computation that only runs, a block, a match, a loop, an exit, a
        // scope, an access, a session action, a hold or a migration, binds
        // what it returns. Any other pattern splits what `e` returns, a value
        // returned, and so does a name over an exercise that places a buffer.
        let runs_only = matches!(
            self.cx().form_at(bound)?,
            Some((
                _,
                Former::Block
                    | Former::Return
                    | Former::Exit
                    | Former::Become
                    | Former::Loop
                    | Former::While
                    | Former::For
                    | Former::Break
                    | Former::Continue
                    | Former::Case
                    | Former::If
                    | Former::Scope
                    | Former::Access
                    | Former::Offer
                    | Former::Action
                    | Former::World
            ))
        );
        if runs_only
            || !matches!(self.cx().form_at(binder)?, Some((_, Former::Name)))
            || (annotation.is_none()
                && Capability::new(self.host()).placing(statement, frame, bound)?
                    == capability::Reply::Minted)
        {
            let _result = self.cx_mut().results.insert(bound.node);
            return self.bound_statement(statement, (binder, annotation, bound), frame);
        }
        let name = self.shared().binder_name(statement, binder)?;
        self.note_binder(binder, frame, name)?;
        let _bound = self.cx_mut().let_bound.insert(bound.node);
        // The stated type is read first. A constructor of a family with
        // arguments takes it as its classifier, as under an annotation
        // `(e : T)`; a family of neither classifies its constructors alone.
        // With no stated type, a family with indices and no parameters gives
        // the constructor its generator's result (#5050).
        let applied = match Native::new(self.host()).applied_constructor(statement, bound)? {
            Maybe::Present(constructor)
                if NativeRef::over(self.cx()).classifies_alone(constructor)
                    == native::Alone(false) =>
            {
                Some(constructor)
            },
            Maybe::Present(_) | Maybe::Absent(_) => None,
        };
        let binding = if let Some(annotation) = annotation {
            self.read(annotation.node, Reading::ValueType(frame));
            if applied.is_some() {
                let _first = self
                    .cx_mut()
                    .classifiers
                    .insert(bound.node, annotation.node);
            }
            StatementBinding::TypedLet {
                name: binder.node,
                annotation: annotation.node,
            }
        }
        else {
            if let Some(constructor) = applied {
                self.resulted(bound, constructor)?;
            }
            StatementBinding::Let(binder.node)
        };
        self.read(bound.node, Reading::Value(frame));
        self.cx_mut().statements.push(Statement {
            origin: lead.node,
            bound: bound.node,
            binding,
            rest: exits::Rest::Bound,
        });
        let bound_at = match annotation {
            Some(annotation) => self.cx_mut().scope.extend_typed(
                frame,
                name,
                annotation.node,
                Maybe::Present(binder.span),
            ),
            None => self
                .cx_mut()
                .scope
                .extend(frame, name, Maybe::Present(binder.span)),
        };
        if annotation.is_none() {
            let _first = self.cx_mut().ran.insert(bound_at, (frame, bound));
        }

        Ok(Frame::Inner(bound_at))
    }

    /// Give the constructor `constructor`, which a `let` with no type binds at
    /// `bound`, the classifier its generator's result states.
    ///
    /// # Specification
    /// - requires: `constructor` is the constructor `bound` applies, and its
    ///   family has parameters or indices.
    /// - ensures: a constructor of a written family with indices and no
    ///   parameters inherits [`native::Classifier::Resulted`] at `bound`; any
    ///   other constructor inherits nothing.
    /// - fails: [`LoweringRefusal::UnfixedParameter`] naming the family's first
    ///   parameter, for a written family with parameters.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnfixedParameter`] for a family with parameters.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `let x = Here(g, a)` classifies `Here` by its result,
    ///   and `let x = B(n)` of a family `B(a : Type)` is refused.
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_untyped_let_reads_its_constructor_s_classifier_off_its_result_5050`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_untyped_let_of_a_parameterised_constructor_names_its_parameter_5050`
    #[spec(ensures: |ret| ret.is_err() == matches!(constructor.form, Generators::Written(form) if self.cx().collected.data.get(form).is_some_and(|data| !data.parameters.is_empty())))]
    fn resulted(
        &mut self,
        bound: Placed,
        constructor: Constructor,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Generators::Written(form) = constructor.form
        else {
            return Ok(());
        };
        let Some(data) = self.cx().collected.data.get(form)
        else {
            return Ok(());
        };
        // A generator's result applies the family to its own parameters, so
        // no field fixes one.
        if let Some(parameter) = data.parameters.first() {
            return Err(LoweringRefusal::UnfixedParameter {
                span: bound.span,
                constructor: self.cx().name_at(constructor.named),
                parameter: self.cx().name_at(parameter.named),
            });
        }
        if !data.indices.is_empty() {
            let _first = self.cx_mut().inherited.insert(
                bound.node,
                native::Classifier::Resulted(native::ResultOf {
                    form,
                    generator: constructor.tag,
                }),
            );
        }
        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The component patterns of a tuple pattern `(p, q)` or a product
    /// pattern `*{p, q}` standing as a `let` statement's binder, in order.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: each component of a tuple or a product pattern, in order,
    ///   with its label when it is written `.l` or `.l = p`: the label tile
    ///   itself is the component of a punned `.l`; the two patterns of the same
    ///   components give the same components; absent for any other pattern.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and a
    ///   fault naming the `let` statement for a repaired pattern or a tile out
    ///   of place among the components.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-component tuple binds both names in order, and
    ///   three components bind all three, and a name pattern reads as no tuple;
    ///   a labelled group binds each output by its label.
    /// - witness: `gandr-surface-lowering::lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `gandr-surface-lowering::lower::tests::a_split_of_three_components_lowers`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_labelled_pattern_binds_each_output_by_its_label`
    /// - witness: `gandr-surface-lowering::lower::tests::a_product_binder_splits_as_the_tuple_binder_4853`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |components| match *components { Maybe::Present(ref parts) => parts.len() >= 2, Maybe::Absent(_) => true }))]
    fn tuple_binders(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<Maybe<TupleComponents, untupled::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(binder.node)
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        let Shape::Form { name, .. } = shape_of(self.cx().pbg, node)?
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        let (open, close) = match name {
            FormName::TUPLE_PATTERN => (TileName::PAREN_OPEN, TileName::PAREN_CLOSE),
            FormName::TELESCOPE_PATTERN => (TileName::RECORD, TileName::BRACE_CLOSE),
            _ => return Ok(Maybe::Absent(untupled::Absent::OtherPattern)),
        };
        let mut pieces = Pieces::new();
        read_pieces(self.cx().pbg, self.cx().tree, binder.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(name));
        }
        let mut cursor = Cursor::new(&pieces.pieces, binder.span);
        closed(statement, &mut cursor, open)?;
        let mut components = Vec::new();
        loop {
            let component = if let Maybe::Present(_dot) = cursor.tile(TileName::DOT) {
                let Maybe::Present(label) = cursor.tile(TileName::IDENTIFIER)
                else {
                    return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
                };
                match cursor.tile(TileName::EQUALS) {
                    Maybe::Present(_) => (Some(label), statement.one(cursor.operands())?),
                    Maybe::Absent(_) => (Some(label), label),
                }
            }
            else {
                (None, statement.one(cursor.operands())?)
            };
            components.push(component);
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(close)
            {
                continue;
            }
            closed(statement, &mut cursor, close)?;
            break;
        }
        if components.len() < 2 {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        }
        Ok(Maybe::Present(components))
    }

    /// The name a `let` statement's pattern binds.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: the name an identifier pattern spells; the empty name, which
    ///   no identifier resolves to, for a wildcard, so `let _ = c;` discards
    ///   `c`'s value at any type.
    /// - provides: the binder reading of the `let` statement.
    /// - fails: yields the unadmitted refusal, at pattern sort and by the
    ///   pattern's own name, for every other pattern;
    ///   [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary `let` binders introduce the spelled name, a
    ///   wildcard binds a name nothing reads, and other patterns are refused
    ///   rather than becoming ordinary names. The predicate asks for the
    ///   binder's own source bytes, by address and length, rather than reading
    ///   the name.
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `gandr-surface-lowering::lower::tests::a_discarded_statement_splits_its_unit`
    /// - witness: `gandr-surface-lowering::lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |name| {
                self.cx().tree.node(binder.node).is_some_and(|node| {
                    match shape_of(self.cx().pbg, node) {
                        | Ok(Shape::Form {
                            former: Former::Name,
                            ..
                        }) => core::ptr::eq(
                            core::ptr::from_ref::<str>(name.as_ref()),
                            core::ptr::from_ref::<str>(self.cx().name_at(binder).as_ref()),
                        ),
                        | Ok(Shape::Form { name: form, .. }) => {
                            form == FormName::WILDCARD && name.as_ref().is_empty()
                        },
                        | _ => false,
                    }
                })
            })
        },
    )]
    fn binder_name(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<SurfaceName<'source>, LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(binder.node)
        else {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        };
        match shape_of(self.cx().pbg, node)? {
            Shape::Form {
                former: Former::Name,
                ..
            } => Ok(self.cx().name_at(binder)),
            Shape::Form { name, .. } if name == FormName::WILDCARD => Ok(SurfaceName::from("")),
            Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: binder.span,
                form: name,
                sort: FragmentSort::Pattern,
                boundary: FragmentBoundary::Unadmitted(unread_pattern(name)),
            }),
            Shape::Repair(repair) => Err(statement.fault(binder.span, FormFault::Repaired(repair))),
            Shape::Root | Shape::Layout => {
                Err(statement.fault(binder.span, FormFault::MisplacedTile))
            },
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify a keyword form of one value operand: `ret v`, `return v` or
    /// `force v`.
    ///
    /// # Specification
    /// - requires: `site` is a returner, a return or a force in term position,
    ///   whose keyword tile is `keyword`.
    /// - ensures: the form standing as a computation reads its one operand as a
    ///   value in its own frame and is planned over it; a return is planned as
    ///   the returner and recorded as an exit, which leaves the function
    ///   because the commuting puts every exit where the function's body ends.
    ///   A return in a handled subject is recorded as crossing its handlers'
    ///   frames, and the body around the scope as delimited: it leaves that
    ///   body past every frame, no return clause run. The operand of a `pure`
    ///   where a body ends, and of a return, is classified by the type the body
    ///   answers. A returner whose whole operand is an annotation `(e : T)`
    ///   records `T` as that operand's ascription, which the mint returns at.
    /// - provides: the computation formers over a value, and the exit that
    ///   leaves a function with a value.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a return that stands where no path through a
    ///   function's, a lambda's or a thunk's body passes, a scope's subject
    ///   included, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force and return plan their own former over a value
    ///   operand, and an author-written force is not marked as inserted; a
    ///   return on a path lowers as the returner and one in a call's head is
    ///   refused; an annotated operand is returned ascribed.
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotated_return_is_ascribed_its_returner_1107`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.cx().plans.get(site.at.node) {
                    | Some(&Plan::Force(operand)) => {
                        keyword == TileName::FORCE
                            && self.cx().reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | Some(&Plan::Return(operand)) => {
                        keyword != TileName::FORCE
                            && (keyword != TileName::RETURN
                                || (self.cx().exitable.contains(&site.at.node)
                                    && self.cx().leaving.contains(&site.at.node)
                                    && self.cx().framed.contains(&site.at.node)
                                        == self.cx().crossing.contains(&site.at.node)))
                            && self.cx().reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | _ => false,
                }
        },
    )]
    fn keyed(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        keyword: TileName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if keyword == TileName::RETURN {
            if !self.cx().exitable.contains(&site.at.node) {
                return Err(site.out(FragmentBoundary::NotInTail));
            }
            if self.cx().framed.contains(&site.at.node) {
                let Some(&body) = self.cx().bodies.get(&site.at.node)
                else {
                    return Err(site.out(FragmentBoundary::NotInTail));
                };
                let _crossing = self.cx_mut().crossing.insert(site.at.node);
                let _delimited = self.cx_mut().delimited.insert(body);
            }
            let _exit = self.cx_mut().leaving.insert(site.at.node);
        }
        let _keyword = cursor.tile(keyword);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        if keyword != TileName::FORCE
            && let Some((_, classifier)) = Native::new(self.host()).annotation(operand.node)?
        {
            let _first = self.cx_mut().ascribed.insert(operand.node, classifier);
        }
        self.read(operand.node, Reading::Value(frame));
        // The value a tail's `pure` or a `return` returns is the one the body
        // answers.
        let answer = if keyword == TileName::PURE && self.cx().exits.contains(&site.at.node) {
            self.cx().answers.get(&site.at.node)
        }
        else if keyword == TileName::RETURN {
            self.cx()
                .bodies
                .get(&site.at.node)
                .and_then(|body| self.cx().answers.get(body))
        }
        else {
            None
        };
        if let Some(&answer) = answer {
            let _first = self
                .cx_mut()
                .inherited
                .insert(operand.node, native::Classifier::Answered { answer, frame });
        }
        let plan = if keyword == TileName::FORCE {
            Plan::Force(operand.node)
        }
        else {
            Plan::Return(operand.node)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// Classify a run written where a value is read, `run c`.
    ///
    /// # Specification
    /// - requires: `site` is a run in term position.
    /// - ensures: the form standing as a value reads its one operand as a
    ///   computation in its own frame and is planned as the run over it; the
    ///   checker's elaboration binds the computation before the computation
    ///   around it.
    /// - provides: the written form of the bridge a computation in value
    ///   position otherwise takes inferred.
    /// - fails: yields the wrong-sort refusal where no bridge reaches a value,
    ///   and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written run plans the run over its computation
    ///   operand, marked written rather than inserted, and its operand is read
    ///   as a computation, so a value operand is refused by sort.
    /// - witness: `gandr-surface-lowering::lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Run(operand))
                    if self.cx().reading(operand) == Reading::Computation(site.reading.frame()))
        },
    )]
    fn run(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::RUN);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Computation(frame));
        self.plan(site, Plan::Run(operand.node));

        Ok(())
    }

    /// Classify a tail call, `become c`.
    ///
    /// # Specification
    /// - requires: `site` is a `become` in term position.
    /// - ensures: the form standing as a computation where a path through a
    ///   function's, a lambda's or a thunk's body passes reads its one operand
    ///   as a computation in its own frame, the answer its position states
    ///   passed on, is recorded as an exit and adopts the operand: the operand
    ///   runs under the caller's continuation, so the exit adds the guarantee,
    ///   not a frame. The operand is not itself where the body ends: `become`
    ///   is the exit, so the operand needs none; a path passes it, so an exit
    ///   inside it leaves the function too.
    /// - provides: the exit that leaves a function by running a computation.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a `become` where no path passes,
    ///   [`LoweringRefusal::AcrossHandler`] for one in a handled subject, which
    ///   would run its operand in place of a live handler's frame, and the
    ///   hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `become` ending a body lowers as its operand, one
    ///   in a bound computation leaves the function, and one in a call's head
    ///   is refused.
    /// - witness: `gandr-surface-lowering::lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_exit_that_would_run_in_a_live_frame_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Transparent(operand))
                    if self.cx().exitable.contains(&site.at.node) && self.cx().leaving.contains(&site.at.node)
                        && !self.cx().exits.contains(&operand) && self.cx().exitable.contains(&operand)
                        && self.cx().reading(operand) == Reading::Computation(site.reading.frame()))
        },
    )]
    fn tail_call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.cx().exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        if self.cx().framed.contains(&site.at.node) {
            return Err(LoweringRefusal::AcrossHandler {
                span: site.at.span,
                exit: CrossedExit::Become,
            });
        }
        let _exit = self.cx_mut().leaving.insert(site.at.node);
        let _keyword = cursor.tile(TileName::BECOME);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Computation(frame));
        if let Some(&answer) = self.cx().answers.get(&site.at.node) {
            let _passed = self.cx_mut().answers.insert(operand.node, answer);
        }
        let _path = self.cx_mut().exitable.insert(operand.node);
        if let Some(&body) = self.cx().bodies.get(&site.at.node) {
            let _owner = self.cx_mut().bodies.insert(operand.node, body);
        }
        self.plan(site, Plan::Transparent(operand.node));

        Ok(())
    }

    /// Classify an application, `c(v, …)`.
    ///
    /// # Specification
    /// - requires: `site` is a call in term position, or at a type's own
    ///   position inside a type a body quotes.
    /// - ensures: a call whose head is a constructor of a data family declared
    ///   strictly earlier is that constructor applied to the arguments as its
    ///   fields; one whose head is a multi-output constructor is the record of
    ///   its ports over the arguments, as `Native::ports` plans it; a call
    ///   whose head is `here`, `back` or `cong`, a name no binder and no
    ///   earlier declaration carries, is that identity operation over the
    ///   arguments; a call whose head selects an operation off a capability is
    ///   that exercise, one whose head is a continuation — an operation
    ///   clause's, or a binder declared at `Stack(C, D)` or a member
    ///   abbreviating it — resumes it, and one whose head selects a method off
    ///   its receiver is that method's call, as [`Capability::exercise`],
    ///   [`Capability::resumption`] and [`Capability::method`] read them; a
    ///   call standing where a value is read whose head is a type former's
    ///   name, free — `Path` over three arguments, `List(A)`, `Flow`, `Stack`,
    ///   `Run` — is the type it spells, as [`Self::applied_head`] plans it,
    ///   quoted, and one whose head names a data or a codata family is that
    ///   family's type over the arguments, as [`Self::static_application`]
    ///   plans it, quoted, so `Box(Integer)` passed for a type parameter is the
    ///   type (#2512); a call standing where a type is read is the type
    ///   application it spells, as
    ///   [`Self::typed_call`](crate::lower::Expressions::typed_call) plans it;
    ///   any other call standing as a computation reads its head at the head
    ///   position and each argument as a value, all in its own frame, a model
    ///   implicit's components and an omitted instance standing at the call
    ///   itself, and is planned as the head applied to the arguments left to
    ///   right; a call whose head is an instantiation, a recursive call,
    ///   records every argument for the head's claim to check, reads each as a
    ///   value so a later parameter's type can name a leading one, and applies
    ///   those from the staged parameter's on, the ones its fixpoint takes; a
    ///   call of no arguments is its head, whose force [`Self::mint_at`] marks
    ///   as the call the source wrote.
    /// - provides: the elimination of a lambda, curried over any argument
    ///   count.
    /// - fails: yields the wrong-sort refusal outside computation position
    ///   where no type is read, the refusals of
    ///   [`Self::typed_call`](crate::lower::Expressions::typed_call) where one
    ///   is, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the argument count is separated by none, one and two,
    ///   each asserted as the exact application chain read back out of the
    ///   arena. The predicate reads only the operands this call appended.
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_bound_name_shadows_an_identity_operation`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_at_a_quoted_path_carrier_unquotes_as_at_a_binder_3573`
    #[spec(
        captures: start = self.cx().operands.mark(),
        ensures: |ret| {
            ret.is_err()
                || match self.cx().plans.get(site.at.node) {
                    | Some(&Plan::Application(head, arguments)) => {
                        let written = self.cx().operands.since(start);
                        let positions = self.shared().spread(arguments);
                        let descends = self.cx().descents.get(&head).is_some_and(|descent| {
                            descent.arguments == written && descent.call == site
                        });
                        (arguments == written
                            || (descends
                                && (arguments == FormStretch::default()
                                    || positions.end == self.cx().operands.entries().len())))
                            && self.cx().reading(head) == Reading::Head(site.reading.frame())
                            && (positions.start .. positions.end).all(|position| {
                                self.cx().operands.locate(At::from(position)).is_some_and(|key| {
                                    self.cx().nominated.contains_key(&key)
                                        || self.cx().components.contains_key(&key)
                                        || self.cx().instanced.contains_key(&key)
                                })
                                    || self.cx().operands.entries().get(position).is_some_and(|&argument| {
                                        self.cx().reading(argument) == Reading::Value(site.reading.frame())
                                    })
                            })
                    },
                    | Some(&(Plan::Constructor(constructed) | Plan::Ports(constructed, _))) => {
                        constructed.fields == self.cx().operands.since(start)
                    },
                    | Some(&(Plan::Here(_) | Plan::Funext(..) | Plan::Equiv(..) | Plan::Univalence(_) | Plan::PathProduct(..) | Plan::Ua { .. } | Plan::Fill { .. } | Plan::Generic | Plan::ListCons(..) | Plan::Transport(..) | Plan::TelescopeTransport(_) | Plan::Derived(_) | Plan::Exercise(_) | Plan::Method(_) | Plan::Resume(..) | Plan::Abandon(_) | Plan::SessionRelated(..) | Plan::Stay(_) | Plan::Forward(_) | Plan::FunctionFlow(..) | Plan::FlowProduct(..) | Plan::FlowThen(..) | Plan::Recorded(_) | Plan::Dialogue(_) | Plan::Decompose(_) | Plan::Ride(..))) => true,
                    | Some(&(Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..) | Plan::Former(..) | Plan::Data(..) | Plan::Codata(..))) => {
                        matches!(site.reading, Reading::Value(_)) || site.reading.family() == Family::Type
                    },
                    | Some(&(Plan::Relation(..) | Plan::Bundle(_))) => site.reading.family() == Family::Type,
                    | Some(&(Plan::Decode(..) | Plan::Unquote(..))) => {
                        site.reading.family() == Family::Type || self.cx().static_calls.contains(&site.at.node)
                    },
                    | Some(&(Plan::StaticApplication(..) | Plan::Called(..))) => {
                        self.cx().static_calls.contains(&site.at.node)
                    },
                    | _ => false,
                }
        },
    )]
    fn call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(constructor) =
                Native::new(self.host()).constructor_head(site, head)?
        {
            self.constructed_at(head.span, constructor);
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let fields = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).construct(site, constructor, fields);
        }
        // A multi-output constructor with no output named is the record of
        // its ports.
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(ported) = Native::new(self.host()).ported_head(site, head)?
        {
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let fields = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).ports(site, ported, fields);
        }
        // A call of a function returning a group of outputs, standing as one
        // value, is the record of its outputs.
        if let Reading::Value(frame) = site.reading
            && let Some(outputs) =
                Models::new(self.host()).called_outputs(frame, site.at, site.at.node)?
        {
            let labels = outputs
                .iter()
                .map(|output| match output.key {
                    arity::Key::Label(name, _) => {
                        Some(FieldLabel::from(String::from(name.as_ref())))
                    },
                    arity::Key::Positional | arity::Key::Index(..) => None,
                })
                .collect();
            let _first = self.cx_mut().packed.insert(site.at.node, labels);
        }
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(operation) =
                Identities::new(self.host()).identity_head(site, head)?
        {
            let _head = cursor.operands();
            return Identities::new(self.host()).identity_call(site, operation, cursor);
        }
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present((former, stratum)) = self.stratum_head(site, head)?
        {
            let _head = cursor.operands();
            return match former {
                ua::Stratified::Ua => self.ua_call(site, stratum, cursor),
                ua::Stratified::Compose => {
                    Identities::new(self.host()).compose_call(site, stratum, cursor)
                },
                ua::Stratified::Fill => {
                    Identities::new(self.host()).fill_call(site, stratum, cursor)
                },
            };
        }
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(derivation) = self.generic_head(site, head)?
        {
            let _head = cursor.operands();
            return self.generic_call(site, derivation, cursor);
        }
        if let Reading::Value(_) = site.reading
            && self.shared().in_static_body(site.at.span) == Within::StaticBody
            && !self.cx().at_endpoint.contains(&site.at.node)
            && self.static_call(site, &mut cursor)? == arity::Planned(true)
        {
            return Ok(());
        }
        if site.reading.family() == Family::Type {
            return self.typed_call(site, cursor);
        }
        if let Reading::Value(_) = site.reading
            && let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(name) = self.former_head(site, head)?
        {
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let written = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return self.applied_head(site, head, name, written, &[]);
        }
        if let Reading::Value(_) = site.reading
            && let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(family) = Native::new(self.host()).family_head(site, head)?
        {
            self.resolved(head.span, family);
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let applied = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return self.static_application(site, family, applied);
        }
        if Capability::new(self.host()).exercise(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        if Capability::new(self.host()).resumption(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        if Capability::new(self.host()).abandonment(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        if Capability::new(self.host()).method(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        let frame = self.require(site, Produced::Computation)?;
        if self.supplied_call(site, frame, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        let head = site.one(cursor.operands())?;
        let start = self.cx().operands.entries().len();
        arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
        let descends = self.cx().tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Instantiation,
                    ..
                })
            )
        });
        // A descent omits its function's implicits and instances, as any call
        // may.
        if descends {
            let omitted = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            Native::new(self.host()).omitted_entries(site, frame, head, omitted)?;
        }
        let written = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        let applied = if descends {
            let cx = self.cx_mut();
            let _first = cx.descents.insert(head.node, native::Descent {
                call: site,
                arguments: cx.kept(written),
            });
            let leading = Native::new(self.host()).leading_parameters(frame, head)?.0;
            Stretch {
                start: written.start.saturating_add(leading).min(written.end),
                end: written.end,
            }
        }
        else {
            written
        };
        if applied.start == applied.end {
            let _first = self.cx_mut().nullary.insert(head.node, site.at.node);
        }
        // A descent writes every argument, the leading ones it leaves out of
        // its application among them, so its parameters pair with all of
        // them, and each is read: a type a later parameter takes from a
        // leading one names it as written.
        Native::new(self.host()).parameters_classify(site, frame, head, written)?;
        self.read(head.node, Reading::Head(frame));
        for position in written.start .. written.end {
            if self
                .cx()
                .operands
                .locate(At::from(position))
                .is_some_and(|key| {
                    self.cx().instanced.contains_key(&key)
                        || self.cx().nominated.contains_key(&key)
                        || self.cx().components.contains_key(&key)
                        || self.cx().kept_implicits.contains(&key)
                })
            {
                continue;
            }
            if let Some(&argument) = self.cx().operands.entries().get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Application(head.node, self.cx().kept(applied)));

        Ok(())
    }

    /// A call standing where a type is read: the type application it spells.
    ///
    /// The expression grammar molds a type quoted in a body, so a call at a
    /// type's own position there, a path type's carrier, is a call form. Read
    /// as the type application it spells, it is the type that application is
    /// in a binder's type.
    ///
    /// # Specification
    /// - requires: `site` reads a type, and `cursor` holds the call's pieces.
    /// - ensures: a head that is one name or one capitalised name, resolving to
    ///   a binder or a declaration, applied to the arguments as
    ///   [`Self::static_application`] plans it: a family's type, the decode of
    ///   a static application, or the unquote of a function's call. A descent
    ///   head `f[<]`
    ///   ([`Self::descent_head`](crate::lower::Expressions::descent_head))
    ///   applied to the arguments is the unquote of its fixpoint's call, as
    ///   `Native::staged_descent` plans it. A head spelling a type former,
    ///   `Path[.A = A](x, y)`, is that former as [`Self::applied_head`] reads
    ///   it. Any other head is refused by its sort.
    /// - provides: a quoted type's call read as the same type its binder's type
    ///   writes.
    /// - fails: the wrong-sort refusal for a head that is not a resolving name,
    ///   and the refusals of the name's resolution, the arguments and the
    ///   application.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function called at a quoted path type's carrier
    ///   unquotes its call, as at a binder's type; a decoder's descent there
    ///   unquotes its fixpoint's call, as in a type.
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_at_a_quoted_path_carrier_unquotes_as_at_a_binder_3573`
    /// - witness: `gandr-surface-lowering::lower::tests::a_descent_at_a_quoted_path_carrier_unquotes_as_in_a_type_3681`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Decode(..) | Plan::Unquote(..) | Plan::Data(..) | Plan::Codata(..) | Plan::Former(..) | Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..) | Plan::Relation(..) | Plan::Bundle(_)))
                )
        },
    )]
    fn typed_call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Run::One(head) = cursor.clone().operands()
        else {
            return Err(self
                .shared()
                .standing(site)
                .out(FragmentBoundary::WrongSort));
        };
        // A descent the expression grammar molds, `f[<](…)`, is the type
        // application `f[<](…)` the type grammar spells (#3681).
        if let Some(named) = self.descent_head(head)? {
            let _first = self.cx_mut().typed_heads.insert(site.at.node, head.node);
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let written = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).staged_descent(site, named, written);
        }
        // A type former the expression grammar molds as a call, `Path[.A =
        // A](x, y)`, is the former the type grammar spells (#4508).
        if let Maybe::Present(name) = self.former_head(site, head)? {
            let _head = cursor.operands();
            let start = self.cx().operands.entries().len();
            arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
            let written = Stretch {
                start,
                end: self.cx().operands.entries().len(),
            };
            return self.applied_head(site, head, name, written, &[]);
        }
        let named = self.cx().tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Name | Former::Constructor,
                    ..
                })
            )
        });
        if !named {
            return Err(self
                .shared()
                .standing(site)
                .out(FragmentBoundary::WrongSort));
        }
        let name = self.cx().name_at(head);
        let _first = self.cx_mut().typed_heads.insert(site.at.node, head.node);
        let at_head = Site { at: head, ..site };
        let Maybe::Present(resolved) = self.resolve_name(at_head, site.reading.frame(), name)?
        else {
            return Err(self
                .shared()
                .standing(site)
                .out(FragmentBoundary::WrongSort));
        };
        self.resolved(head.span, resolved);
        let _head = cursor.operands();
        let start = self.cx().operands.entries().len();
        arguments(site, &mut cursor, &mut self.cx_mut().operands)?;
        let applied = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        self.static_application(site, resolved, applied)
    }

    /// A call written in a static lambda's body, read as the static
    /// application the type grammar spells there (#4508).
    ///
    /// The block of `fun (X) { T }` molds its body in the expression grammar,
    /// so a type application written there, `F(X)`, is a call form. Read as
    /// that application, a head a binder or a declaration answers applies its
    /// code to the arguments as [`Self::static_application`] plans it. A call
    /// at a path type's endpoint there is a value the type relates, read as
    /// the ordinary call it is, so the kernel replays it as the value its run
    /// returns (#4618).
    ///
    /// # Specification
    /// - requires: `site` is a call read as a value inside a static lambda's
    ///   body, at no endpoint, and `cursor` holds its pieces.
    /// - ensures: for a head that is one name or one capitalised name resolving
    ///   to a binder or a declaration, the static application of it to the
    ///   arguments, the cursor past them; nothing planned and the cursor
    ///   untouched for any other head.
    /// - provides: a static body's type application spelled as a call.
    /// - fails: the refusals of the name's resolution, the arguments and the
    ///   application.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a static lambda over a binder holding an operator
    ///   applies it to its own binder, read back as the static application.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |planned| !planned.0 || (self.cx().plans.get(site.at.node).is_some() && self.cx().static_calls.contains(&site.at.node))))]
    fn static_call(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let Run::One(head) = cursor.clone().operands()
        else {
            return Ok(arity::Planned(false));
        };
        let named = self.cx().tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Name | Former::Constructor,
                    ..
                })
            )
        });
        if !named {
            return Ok(arity::Planned(false));
        }
        let name = self.cx().name_at(head);
        let at_head = Site { at: head, ..site };
        let Maybe::Present(resolved) = self.resolve_name(at_head, site.reading.frame(), name)?
        else {
            return Ok(arity::Planned(false));
        };
        let _first = self.cx_mut().typed_heads.insert(site.at.node, head.node);
        self.resolved(head.span, resolved);
        let _head = cursor.operands();
        let start = self.cx().operands.entries().len();
        arguments(site, cursor, &mut self.cx_mut().operands)?;
        let applied = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        let _first = self.cx_mut().static_calls.insert(site.at.node);
        self.static_application(site, resolved, applied)?;
        Ok(arity::Planned(true))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Whether `span` lies inside a static lambda's body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Within::StaticBody`] exactly when a body
    ///   [`Context::static_spans`](gandr_surface_lowering_base::lower::Context::static_spans)
    ///   records covers `span`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::static_call`](crate::lower::Expressions::static_call).
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body scans the recorded bodies once; the check scans them once more"
        )
    )]
    #[spec(ensures: |ret| (ret == Within::StaticBody) == self.cx().static_spans.iter().any(|body| body.start() <= span.start() && span.end() <= body.end()))]
    fn in_static_body(
        &self,
        span: ByteSpan,
    ) -> Within
    {
        if self
            .cx()
            .static_spans
            .iter()
            .any(|body| body.start() <= span.start() && span.end() <= body.end())
        {
            Within::StaticBody
        }
        else {
            Within::Elsewhere
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The name a call's head descends on, when the head is a descent `f[<]`.
    ///
    /// # Specification
    /// - ensures: the name `f` when `head` is an instantiation of a bare name
    ///   whose bracket holds the one tile `<`; nothing for every other head,
    ///   the productive claim `f[>]` among them.
    /// - provides: [`Self::typed_call`](crate::lower::Expressions::typed_call)'
    ///   s descent head.
    /// - fails: a fault reading the head's pieces or shape.
    /// - panics: none.
    /// - executable: none — the answer is a spelling read off the tree, which
    ///   the name it returns does not carry.
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::typed_call`](crate::lower::Expressions::typed_call).
    /// - witness: `gandr-surface-lowering::lower::tests::a_descent_at_a_quoted_path_carrier_unquotes_as_in_a_type_3681`
    fn descent_head(
        &mut self,
        head: Placed,
    ) -> Result<Option<SurfaceName<'source>>, LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(head.node)
        else {
            return Ok(None);
        };
        if !matches!(shape_of(self.cx().pbg, node)?, Shape::Form {
            former: Former::Instantiation,
            ..
        }) {
            return Ok(None);
        }
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let found = self.shared().descended_name(head.node, &mut scratch);
        self.cx_mut().scratch = scratch;
        found
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The name an instantiation at `at` descends on, read through `scratch`,
    /// as [`Self::descent_head`](crate::lower::Expressions::descent_head)
    /// states it.
    ///
    /// # Specification
    /// - requires: `at` is an instantiation.
    /// - ensures: as
    ///   [`Self::descent_head`](crate::lower::Expressions::descent_head).
    /// - fails: as [`Self::descent_head`](crate::lower::Expressions::descent_head).
    /// - panics: none.
    /// - executable: none — as
    ///   [`Self::descent_head`](crate::lower::Expressions::descent_head).
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::typed_call`](crate::lower::Expressions::typed_call).
    /// - witness: `gandr-surface-lowering::lower::tests::a_descent_at_a_quoted_path_carrier_unquotes_as_in_a_type_3681`
    fn descended_name(
        &self,
        at: NodeIndex,
        scratch: &mut Pieces,
    ) -> Result<Option<SurfaceName<'source>>, LoweringRefusal<'source>>
    {
        read_pieces(self.cx().pbg, self.cx().tree, at, scratch)?;
        let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
            Piece::Operand(operand) => Some(operand),
            Piece::Tile { .. } => None,
        });
        let (Some(named), Some(claim)) = (operands.next(), operands.next())
        else {
            return Ok(None);
        };
        let bare = self.cx().tree.node(named.node).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            )
        });
        if !bare {
            return Ok(None);
        }
        read_pieces(self.cx().pbg, self.cx().tree, claim.node, scratch)?;
        if !matches!(scratch.pieces.as_slice(), &[Piece::Tile { label, .. }] if label == TileName::LESS_THAN)
        {
            return Ok(None);
        }
        Ok(Some(self.cx().name_at(named)))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Lower native prefix and infix syntax using the shared vocabulary.
    ///
    /// # Specification
    /// - ensures: the table row selected by the operator receives value
    ///   operands in source order; an infix `==`, `<`, `<=`, `>` or `>=` in a
    ///   unit that lays the prelude is instead the call of the prelude's
    ///   declaration of the row's name, its model of `Eq` or `Ord` resolved
    ///   from the operands ([`Self::through_prelude`]); a prefix `-` written
    ///   directly on a natural literal is one negative integer literal, a
    ///   value, so `-4` stands at `Integer` with no call and reads through
    ///   `FromNeg` elsewhere (#4732); a prefix `-` written directly on a bare
    ///   fraction is one negative decimal literal, read at its type as the
    ///   fraction is (#4807); a prefix `-` before a number written with the
    ///   `f64` suffix is `float64.neg`, so the printers' spelling of a negative
    ///   float, `-0.5f64`, lowers back to that float; the infix `then` is the
    ///   composite of two paths, or of two flows where a flow is answered, as
    ///   [`Identities::derive`] plans it; the cons `g ∷ p` is a word, as
    ///   `Native::cons` plans it; `left |> right` plugs every output of `left`
    ///   into `right`, as `Models::plug` plans it.
    /// - fails: malformed tiles or operators outside the admitted vocabulary
    ///   are refused; `then` refuses as [`Identities::derive`] does, and the
    ///   cons as `Native::cons` does.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the form or fragment refusal at the source operator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric operands separate order and operator
    ///   choice; unsupported operators are rejected; a prefix operator takes
    ///   its one operand.
    /// - witness: `gandr-surface-lowering::lower::tests::native_operator_plans_preserve_order`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `gandr-surface-lowering::lower::tests::a_prefix_operator_takes_its_one_operand`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_plugging_passes_every_output_in_order`
    /// - witness: `gandr-surface-lowering::lower::tests::a_negated_float_literal_is_float64_negation_1830`
    /// - witness: `gandr-surface-lowering::lower::tests::a_negated_natural_literal_is_one_negative_literal_4732`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decimal_reads_as_its_exact_value_4807`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::equality_calls_the_prelude_s_eq_2302`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::an_order_calls_the_prelude_s_order_2333`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.cx().plans.get(site.at.node), Some(Plan::PrimitiveCall(..) | Plan::Application(..) | Plan::Derived(_) | Plan::FlowThen(..) | Plan::Constructor(_) | Plan::Plugged { .. } | Plan::Literal(Literal::Integer(_) | Literal::Numeric(_)))))]
    fn operator(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        use gandr_core_term::primitive::Arguments;
        use gandr_core_term::primitive::Operator;
        use gandr_core_term::primitive::PRELUDE;
        if let &[
            Piece::Operand(letter),
            Piece::Tile { label, .. },
            Piece::Operand(rest),
        ] = pieces.pieces.as_slice()
            && label == TileName::CONS
        {
            return Native::new(self.host()).cons(site, letter, rest);
        }
        if let &[
            Piece::Operand(left),
            Piece::Tile { label, .. },
            Piece::Operand(right),
        ] = pieces.pieces.as_slice()
            && label == TileName::PLUG
        {
            return Models::new(self.host()).plug(site, left, right);
        }
        // `-n` written on a natural literal is one negative literal: a value,
        // primitive at `Integer` and read through `FromNeg` at another type.
        if let [Piece::Tile { label, .. }, Piece::Operand(operand)] = *pieces.pieces.as_slice()
            && label.as_ref() == "-"
            && let Maybe::Present(Literal::Integer(natural)) =
                parse_literal(Former::Number, self.cx().text_at(operand))
        {
            let _frame = self.require(site, Produced::Value)?;
            let negative = IntegerLiteral::new(Sign::Negative, natural.magnitude().clone());
            self.plan(site, Plan::Literal(Literal::Integer(negative)));
            self.cx_mut().covers.push((site.at.span, operand.span));
            return Ok(());
        }
        // `-d` written on a bare fraction is one negative decimal, read at its
        // type as the fraction is.
        if let [Piece::Tile { label, .. }, Piece::Operand(operand)] = *pieces.pieces.as_slice()
            && label.as_ref() == "-"
            && let Maybe::Present(decimal) = decimal_literal(self.cx().text_at(operand))
        {
            let _frame = self.require(site, Produced::Value)?;
            let negative = NumericLiteral::new(
                Sign::Negative,
                decimal.integer_part().clone(),
                decimal.fraction().clone(),
            );
            self.plan(site, Plan::Literal(Literal::Numeric(negative)));
            self.cx_mut().covers.push((site.at.span, operand.span));
            return Ok(());
        }
        let frame = self.require(site, Produced::Computation)?;
        let (label, tile, arguments) = match *pieces.pieces.as_slice() {
            [Piece::Tile { label, at }, Piece::Operand(argument)] => {
                (label, at, Arguments::Unary(argument.node))
            },
            [
                Piece::Operand(first),
                Piece::Tile { label, at },
                Piece::Operand(second),
            ] => (label, at, Arguments::Binary([first.node, second.node])),
            _ => return Err(site.fault(site.at.span, FormFault::MisplacedTile)),
        };
        // A negated `f64`-suffixed number is the float's negation: the integer
        // row would refuse its operand, and the printers write a negative float
        // so.
        let negated = label.as_ref() == "-"
            && match arguments {
                Arguments::Unary(operand) => {
                    self.cx().tree.fragment(operand).is_some_and(|written| {
                        let written: &str = written.as_ref();
                        written
                            .strip_suffix("f64")
                            .is_some_and(|digits| digits.parse::<Float64Literal>().is_ok())
                    })
                },
                Arguments::Binary(_) => false,
            };
        let Some(&primitive) =
            PRELUDE
                .iter()
                .find(|primitive| match (primitive.operator(), arguments) {
                    _ if negated => primitive.name().as_ref() == "float64.neg",
                    (Operator::Prefix(spelling), Arguments::Unary(_))
                    | (Operator::Infix(spelling), Arguments::Binary(_)) => {
                        spelling == label.as_ref()
                    },
                    _ => false,
                })
        else {
            let feature = if let Arguments::Unary(_) = arguments {
                Unbuilt::PrefixOperator
            }
            else {
                Unbuilt::InfixForm
            };
            return Err(site.out(FragmentBoundary::Unadmitted(feature)));
        };
        if let Arguments::Binary(operands) = arguments
            && let Operator::Infix(spelling) = primitive.operator()
            && THROUGH_PRELUDE.contains(&spelling)
            && self.through_prelude(
                site,
                frame,
                (
                    tile,
                    SurfaceName::from(<&'static str>::from(primitive.name())),
                ),
                operands,
            )? == arity::Planned(true)
        {
            return Ok(());
        }
        for argument in arguments.iter() {
            self.read(*argument, Reading::Value(frame));
        }
        self.plan(site, Plan::PrimitiveCall(primitive, arguments));
        Ok(())
    }

    /// Classify a selection `e.name` or `e.0`.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: a selection `Family.Constructor` naming a constructor of a
    ///   family is that constructor, applied to no field, as
    ///   `Native::construct` reads it; a selection `C(a, …).l` off a
    ///   multi-output constructor is its port `l`, as `Native::port` reads it;
    ///   a selection by position projects the entry at that place of the type
    ///   written for its operand, or of the pair the operand is when no type is
    ///   written, as `Models::positional` reads it; a selection read as a
    ///   computation off a name whose written type is a thunked lazy record
    ///   over labels observes the entry its label names; a selection off a name
    ///   whose written type is a type over labels projects the entry its label
    ///   names, as `Models::selection` reads it; a selection off a name whose
    ///   written type is a data family without indices reads the field its
    ///   label names off every constructor, as `Native::data_field` reads it; a
    ///   selection off a flattened model implicit is the parameter of the
    ///   component it names, as `Models::flattened_member` reads it; a
    ///   selection off a value no written type states, a chain of selections
    ///   ending at a binder's or a declaration's name not capitalised, or one
    ///   link off a name written at a patched type, projects the field its
    ///   label names of the record the value is, as `Models::field` reads it. A
    ///   chain of selections whose head is a capitalised name is a path: inside
    ///   a functor whose parameter the head names, a one-link path is that
    ///   parameter's value component, as [`Self::parameter_value`] reads it; a
    ///   path whose head, capitalised or not, names a module an enclosing
    ///   module declares reaches the member that module exports, as
    ///   [`Self::enclosed_member`] reads it, and stands as that member's
    ///   constant as below; otherwise it is resolved through the outermost
    ///   scope, its head the module the path's source sees
    ///   ([`Self::see_module`](crate::lower::Expressions::see_module)), at the
    ///   depth that binds it: a path ending at an exported value component
    ///   stands as that member's constant when the member is declared strictly
    ///   before the declaration the path is written in, its last segment kept
    ///   as a written name resolved to that declaration, and a path ending at a
    ///   type component stands as its stated type, as [`Self::module_type`]
    ///   reads it. The chain is walked by an explicit loop, and its links are
    ///   left unread.
    /// - provides: the governed reading of a module path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a selection a governing module
    ///   or a parameter does not export; [`LoweringRefusal::PartialField`] for
    ///   a data field some constructor does not declare; the forward-member
    ///   refusal for a member declared at or after the referring declaration;
    ///   [`LoweringRefusal::ProjectionFromApplication`] for a chain whose head
    ///   is an application of a functor; the wrong-sort refusal for a path
    ///   ending at a module, which is not a value; the wrong-sort refusal
    ///   outside value position; and the unadmitted refusal for a selection no
    ///   module governs and no value heads: a builtin namespace's member, or a
    ///   field of a name whose written type is neither a record nor a data
    ///   family without indices.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to an exported component at depth two and at
    ///   depth nine, to a hidden member, to an absent member at each depth, to
    ///   a module, to a member declared later, and a selection off a free name,
    ///   each asserted as the exact constant or refusal; a path past a
    ///   parameter's value, refused at that link; a nested module's member
    ///   named from inside its enclosing module and from inside a sibling, a
    ///   member its signature hides, and a module declared after the use.
    /// - witness: `gandr-surface-lowering::tests::modules::a_user_module_selection_is_governed_and_a_free_target_still_projects`
    /// - witness: `gandr-surface-lowering::tests::modules::a_nested_module_is_named_from_inside_its_enclosing_module_1106`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `gandr-surface-lowering::tests::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_namespace_is_not_a_projectable_record`
    /// - witness: `gandr-surface-lowering::tests::modules::a_hidden_or_absent_user_module_component_is_declined_as_a_hole`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::an_observation_projects_its_entry`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_field_of_a_record_no_type_states_projects_its_label_1106`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_some_constructor_lacks_is_refused_1106`
    /// - witness: `gandr-surface-lowering::lower::tests::each_use_of_a_deprecated_declaration_is_listed`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_parameter_is_read_only_inside_its_functor`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_module_supplied_for_a_model_implicit_passes_its_members_739`
    /// - witness: `gandr-surface-lowering::lower::patched::tests::a_selection_off_a_patched_name_projects_its_field_5579`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Constant(_) | Plan::Primitive(_) | Plan::Observe(..) | Plan::Select(..) | Plan::Field(..) | Plan::SubRecord(..) | Plan::Projected(_) | Plan::SelectedOutput { .. } | Plan::Data(..) | Plan::Codata(..) | Plan::Constructor(_) | Plan::Transparent(_) | Plan::Sealed(_) | Plan::Instantiated(..) | Plan::Variable(..) | Plan::StaticApplication(Code::Bound { .. }, _)))
                )
        },
    )]
    fn projection(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // `r.#{ .a, .b }` selects the record of `r`'s fields `a` and `b`.
        if let [_, Piece::Tile { label, .. }, ..] = *pieces.pieces.as_slice()
            && label == TileName::SUB_RECORD_OPEN
        {
            return Models::new(self.host()).sub_record(site, pieces);
        }
        // `Family.Constructor` names a constructor of the family.
        if let Maybe::Present(constructor) =
            Native::new(self.host()).selected_constructor(site, site.at)?
        {
            self.constructed_at(site.at.span, constructor);
            let none = Stretch {
                start: self.cx().operands.entries().len(),
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).construct(site, constructor, none);
        }
        // `C(a, …).l` names the port `l` of the multi-output constructor `C`.
        if Native::new(self.host()).port(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        // `f(a, …).l` selects the output `l` of a call returning a group.
        if Models::new(self.host()).selected_output(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        // An observation by position of a thunked lazy product or codata
        // family comes before the positional selection of a pair.
        if Models::new(self.host()).observation(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if Models::new(self.host()).positional(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if Models::new(self.host()).selection(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if Models::new(self.host()).model_member(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if Native::new(self.host()).data_field(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        let (head, selected) = Context::link(site, &pieces.pieces, site.at.span)?;
        // The head is a name, or a module path a qualified import binds,
        // `text.greet` of `text.greet.greeting`.
        let named = match self.cx().tree.node(head.node) {
            Some(node) => matches!(shape_of(self.cx().pbg, node)?, Shape::Form {
                former: Former::Name | Former::Projection,
                ..
            }),
            None => false,
        };
        if named && let Maybe::Present(resolved) = self.aliased_member(site, head, selected)? {
            let none = Stretch {
                start: self.cx().operands.entries().len(),
                end: self.cx().operands.entries().len(),
            };
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = NativeRef::over(self.cx()).data_family(constant)
            {
                return Native::new(self.host()).family(site, constant, arity, none);
            }
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = NativeRef::over(self.cx()).codata_family(constant)
            {
                return Native::new(self.host()).codata_type(site, constant, arity, none);
            }
            let frame = self.require(site, Produced::Value)?;
            let plan = self.resolved_term(site, frame, resolved)?;
            self.plan(site, plan);
            return Ok(());
        }
        // A selection off a value no module governs is the field of a record.
        if Models::new(self.host()).field(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        let _frame = self.require(site, Produced::Value)?;
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (mut target, member) = Context::link(site, &pieces.pieces, site.at.span)?;
        links.push((target, member));
        let mut chain = Pieces::new();
        let head = loop {
            self.cx_mut().fuel.spend()?;
            let Some(node) = self.cx().tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
            };
            match shape_of(self.cx().pbg, node)? {
                Shape::Form {
                    former: Former::Projection,
                    ..
                } => {
                    read_pieces(self.cx().pbg, self.cx().tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(repaired.refusal(site.name));
                    }
                    let (inner, selected) = Context::link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                Shape::Form {
                    former: Former::Constructor | Former::Name,
                    ..
                } => break target,
                // `(F a).m` is the selection `F(a).m` writes.
                Shape::Form {
                    former: Former::Parenthesized,
                    ..
                } => {
                    let Some(inner) =
                        Models::new(self.host()).ungrouped_target(target, site.at.node)?
                    else {
                        return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                    };
                    target = inner;
                },
                Shape::Form {
                    former: Former::Call,
                    ..
                } => {
                    self.shared().refuse_applied(target, &mut chain)?;
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                },
                Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                },
            }
        };
        if let Some(&(_, first)) = links.last()
            && self.parameter_value(site, head, first, functor::Deeper(links.len() > 1_usize))?
                == functor::Read::Planned
        {
            return Ok(());
        }
        if let Maybe::Present(member) = self.enclosed_member(site, head, &links)? {
            self.select(site, member)?;
            if let Some(&(_, last)) = links.first()
                && let Some(entry) = self.cx().collected.slots.get(usize::from(member))
            {
                self.resolved(last.span, Resolved::Declaration {
                    constant: entry.constant,
                    declared: Maybe::Absent(binder_type::Absent::Untyped),
                });
            }
            return Ok(());
        }
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.cx().text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.cx().text_at(selected).as_ref()));
        }
        let cx = self.cx_mut();
        let path = NamePath::from(segments);
        cx.collected.reach_declaring(
            cx.collected.unit.source_at(site.at.span.start()),
            cx.name_at(head),
        );
        self.see_module(site, self.cx().name_at(head));
        match self.cx().recognition.resolve_path(&path) {
            PathResolution::Complete(Recognized::BuiltinPrimitive { primitive, .. }) => {
                self.plan(site, Plan::Primitive(primitive));
                Ok(())
            },
            PathResolution::Complete(Recognized::ModuleType) => {
                let Some(&(_, member)) = links.first()
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                };
                self.module_type(site, &path, member, None)
            },
            PathResolution::Complete(Recognized::ModuleComponent) => {
                let Some(&exported) = self.cx().exported.get(&path)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                };
                let member = links.first().map(|&(_, member)| member);
                self.component_value(site, exported, head, member)
            },
            PathResolution::Complete(Recognized::ModuleNamespace) => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
            PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.cx().name_at(prefix),
                    member: self.cx().name_at(selected),
                })
            },
            PathResolution::Complete(_) | PathResolution::Ungoverned => {
                Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)))
            },
        }
    }

    /// Make the outermost scope answer `name` with the top-level module the
    /// source holding `site` sees: the module it declares, else the one its
    /// imports answer, else the nearest one its imports' imports declare. A
    /// unit grafts every top-level module of its sources into one scope, a
    /// later one over an earlier one of the same name, so a source whose
    /// module another source's displaced reads it again here.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when the source holding `site` declares a top-level module or
    ///   instance named `name`, or its imports answer one unambiguously, or one
    ///   source alone among the nearest its imports reach declares one, and the
    ///   outermost scope binds `name` to a module another source declares, the
    ///   scope binds `name` to the seen module's namespace, as
    ///   [`Self::declare_module`] declares it; the scope is unchanged
    ///   otherwise, a builtin's binding among them.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the seen module is the answer of the same lookup
    ///   the body makes, which no predicate on the scope reads again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source reading a module's value and type components
    ///   through its import, or through the import of a source it imports, in
    ///   one unit beside a source declaring a module of the same name before
    ///   it.
    /// - witness: `gandr-surface-lowering::tests::namespace::a_module_path_reads_the_module_its_source_sees_4797`
    fn see_module(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    )
    {
        let source = self.cx().collected.unit.source_at(site.at.span.start());
        let seen = match self.shared().top_module(source, name) {
            Some(own) => own,
            None => match self.cx().collected.imported_module(source, name) {
                Ok(Maybe::Present((imported, _))) => imported,
                Ok(Maybe::Absent(_)) => match self.shared().reached_module(source, name) {
                    Some(reached) => reached,
                    None => return,
                },
                Err(_) => return,
            },
        };
        let Some(named) = self
            .cx()
            .collected
            .structures
            .get(usize::from(seen))
            .map(|entry| entry.named.span)
        else {
            return;
        };
        let path = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        if let Maybe::Present(RecognitionSite::Source(held)) = self.cx().recognition.site(&path)
            && held != named
        {
            self.declare_module(seen);
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The top-level module or instance named `name` that `source` declares.
    ///
    /// # Specification
    /// trivial.
    fn top_module(
        &self,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Option<StructureIndex>
    {
        self.cx()
            .collected
            .modules
            .get(&(Container::TopLevel(source), name))
            .copied()
            .filter(|held| {
                self.cx()
                    .collected
                    .structures
                    .get(usize::from(*held))
                    .is_some_and(|entry| {
                        matches!(entry.stratum, Stratum::Module | Stratum::Instance(_))
                    })
            })
    }

    /// The top-level module named `name` that the nearest sources `source`
    /// reaches through its imports declare, public or not, when one alone
    /// does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the module of the first ring of `source`'s import closure,
    ///   its own imports the first ring, where some source declares one, when
    ///   exactly one source of that ring does; none otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a search of the unit's import graph.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::see_module`](crate::lower::Expressions::see_module).
    /// - witness: `gandr-surface-lowering::tests::namespace::a_module_path_reads_the_module_its_source_sees_4797`
    fn reached_module(
        &self,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Option<StructureIndex>
    {
        let targets =
            |from: SourceIndex| {
                self.cx().collected.imports.of(from).filter_map(|import| {
                    match import.resolution() {
                        ImportResolution::Path(ImportTarget::Source(target)) => Some(target),
                        ImportResolution::Path(_) | ImportResolution::Foreign => None,
                    }
                })
            };
        let mut visited = BTreeSet::from([source]);
        let mut ring = BTreeSet::from([source]);
        loop {
            let next: BTreeSet<SourceIndex> = ring
                .iter()
                .flat_map(|&from| targets(from))
                .filter(|target| !visited.contains(target))
                .collect();
            if next.is_empty() {
                return None;
            }
            visited.extend(next.iter().copied());
            let mut found = next
                .iter()
                .filter_map(|&target| self.top_module(target, name));
            if let Some(first) = found.next() {
                return found.next().is_none().then_some(first);
            }
            ring = next;
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Plan the selection at `site` as the exported member at `target`.
    ///
    /// # Specification
    /// - requires: `target` is the member an exported path resolved to.
    /// - ensures: the member's constant, when the member is declared strictly
    ///   before the declaration `site` belongs to and stands at or below its
    ///   phase.
    /// - provides: the position rule and the phase rule for a path.
    /// - fails: yields [`LoweringRefusal::ForwardMemberReference`] for a member
    ///   declared at or after it; [`LoweringRefusal::PhaseDependence`] and
    ///   [`LoweringRefusal::InertRead`] where
    ///   [`Self::admit_read`](crate::lower::ExpressionsRef::admit_read) refuses
    ///   the read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`] and
    /// [`LoweringRefusal::PhaseDependence`] and [`LoweringRefusal::InertRead`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a backward member becomes its declared constant while
    ///   a forward member is refused at the use, with the declaration retained;
    ///   a parameter's value read inside a type member is refused by phase.
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    /// - witness: `gandr-surface-lowering::tests::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_type_member_never_reads_its_parameter_s_value`
    #[spec(
        ensures: |ret| match self.cx().collected.slots.get(usize::from(target)) {
            | None => ret == Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection))),
            | Some(entry) => {
                if matches!(self.cx().collected.owner_of(site.at.node), Maybe::Present(own) if target >= own)
                {
                    ret == Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: entry.name,
                        declared: entry.named.span,
                    })
                }
                else {
                    matches!(ret, Err(LoweringRefusal::PhaseDependence { .. } | LoweringRefusal::InertRead { .. }))
                        || ret.is_ok()
                            && matches!(self.cx().plans.get(site.at.node), Some(&Plan::Constant(constant)) if constant == entry.constant)
                }
            },
        },
    )]
    fn select(
        &mut self,
        site: Site,
        target: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(entry) = self.cx().collected.slots.get(usize::from(target))
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
        };
        let (constant, name, declared) = (entry.constant, entry.name, entry.named.span);
        if let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
            && target >= own
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name,
                declared,
            });
        }
        self.shared().admit_read(site, target)?;
        self.plan(site, Plan::Constant(constant));

        Ok(())
    }

    /// Classify a bare type head.
    ///
    /// # Specification
    /// - requires: `site` is a primitive type, a type identifier or a type
    ///   variable in type position, or a term name or a capitalised name where
    ///   a type is read.
    /// - ensures: a head standing where a value is read — an argument of a
    ///   type-position call — that names a constructor of a data family
    ///   declared strictly earlier stands as that constructor applied to no
    ///   fields, as [`Self::constructor`] reads it in term position. Otherwise,
    ///   inside a module signature, a head naming a type component written
    ///   before the head's own component stands for what that component reads:
    ///   the type a manifest component names, adopted as it lowered, or the
    ///   atom a sealed component's abstract type declares. Otherwise a head a
    ///   binder answers is that code; past the binders, a head naming a type
    ///   member written before it in its own module or an enclosing one stands
    ///   for that member's type; then a head naming a codata family stands as
    ///   that family's computation type at no arguments; then a head an earlier
    ///   declaration answers is that code, read as the static application of it
    ///   to no arguments. Any other head resolves against the nullary table and
    ///   is planned as its atom, and `Type` as the value universe at the
    ///   fuss-free level.
    /// - provides: the type-head half of resolution, the expansion of a
    ///   manifest type component and a type member, the atom of a sealed one,
    ///   and the decode of a value name in type position.
    /// - fails: yields the wrong-sort refusal for a head whose sort does not
    ///   suit the position and the unresolved-head refusal for a head nothing
    ///   answers.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at the bare universe, a binder
    ///   written at a sorted and levelled one, a binder a `let` bound to a
    ///   type, a declaration, an atom, a constructor where a value is read, a
    ///   manifest component, a sealed one and a type member, each asserted as
    ///   the exact core type read back out of the arena.
    /// - witness: `gandr-surface-lowering::lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `gandr-surface-lowering::lower::tests::a_run_bound_type_and_a_constructor_argument_stand_in_a_type`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::u_and_f_are_names`
    /// - witness: `gandr-surface-lowering::lower::tests::every_type_atom_lowers_to_its_core_type`
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::opaque_ascription_seals`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_is_named_only_after_it_is_written`
    #[spec(
        captures: before = self.cx().manifests.len(),
        ensures: |ret| {
            self.cx().manifests.len() >= before
                && self.cx().manifests.len() <= before.saturating_add(1_usize)
                && (ret.is_err()
                    || matches!(
                        self.cx().plans.get(site.at.node),
                        Some(
                            &(Plan::Transparent(_)
                                | Plan::Sealed(_)
                                | Plan::Instantiated(..)
                                | Plan::Atom(_)
                                | Plan::Universe(_)
                                | Plan::Decode(_, _, _)
                                | Plan::StaticApplication(_, _)
                                | Plan::Data(_, _)
                                | Plan::Codata(_, _)
                                | Plan::Constructor(_))
                        )
                    ))
        },
    )]
    fn type_head(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.cx().name_at(site.at);
        if let Reading::Value(_) = site.reading
            && let Maybe::Present(constructor) =
                Native::new(self.host()).named_constructor(site, name)?
        {
            self.constructed_at(site.at.span, constructor);
            let none = Stretch {
                start: self.cx().operands.entries().len(),
                end: self.cx().operands.entries().len(),
            };
            return Native::new(self.host()).construct(site, constructor, none);
        }
        if let Maybe::Present(stated) = self.stated_named(site, name)? {
            return self.stated_type(site, stated);
        }
        let from = site.reading.frame();
        if let Maybe::Present(resolved) = self.resolve_name(site, from, name)? {
            self.resolved(site.at.span, resolved);
            let none = Stretch {
                start: self.cx().operands.entries().len(),
                end: self.cx().operands.entries().len(),
            };
            return self.static_application(site, resolved, none);
        }
        let _frame = self.require(site, Produced::ValueType)?;
        // The expression grammar molds `Type` as a name, so a type position
        // there reads it as the universe the type grammar's tile spells
        // (#4508).
        let plan = match self.shared().atom(name) {
            Maybe::Present(atom) => Plan::Atom(atom),
            Maybe::Absent(_) if name.as_ref() == TileName::UNIVERSE.as_ref() => {
                Plan::Universe(self.shared().universe_of(site, &mut cursor)?)
            },
            Maybe::Absent(_) => {
                return Err(LoweringRefusal::UnresolvedTypeHead {
                    span: site.at.span,
                    head: site.at.span,
                    name,
                    arity: HeadArity::Nullary,
                });
            },
        };

        self.plan(site, plan);

        Ok(())
    }

    /// Plan the type head at `site` as what the stated type `stated` reads.
    ///
    /// # Specification
    /// - requires: `stated` is a type component or a type member the head
    ///   names.
    /// - ensures: the head is planned as the type a manifest meaning names,
    ///   adopted as it lowered, as the atom a sealed component's abstract slot
    ///   declares, or as an instance's manifest type, its template's renamed by
    ///   the application; either way the reference is recorded against the slot
    ///   carrying the stated type's refusal, so a refusal there reaches the
    ///   declaration the head belongs to.
    /// - provides: the one reading of a stated type, whether named bare or by a
    ///   path.
    /// - fails: yields the wrong-sort refusal where the position reads no type
    ///   of the stated type's sort, a computation type for a manifest or an
    ///   instance's type whose definition is one and a value type otherwise,
    ///   and [`LoweringRefusal::ForwardMemberReference`] for an atom or an
    ///   instance's type the referring declaration does not follow.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component, a type member and a sealed
    ///   component each plan their exact reading, and a sealed one named by a
    ///   declaration before its module is refused by position.
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::opaque_ascription_seals`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[spec(
        captures: before = self.cx().manifests.len(),
        ensures: |ret| {
            ret.is_err()
                || (self.cx().manifests.len() == before.saturating_add(1_usize)
                    && self.cx().manifests.last() == Some(&(stated.held, site.at.node))
                    && match stated.meaning {
                        | TypeMeaning::Manifest(defined) => matches!(self.cx().plans.get(site.at.node), Some(&Plan::Transparent(node)) if node == defined.node),
                        | TypeMeaning::Sealed => matches!(self.cx().plans.get(site.at.node), Some(&Plan::Sealed(atom)) if usize::from(atom) == usize::from(stated.held)),
                        | TypeMeaning::Instantiated { defined, instance } => matches!(self.cx().plans.get(site.at.node), Some(&Plan::Instantiated(read, node)) if read == instance && node == defined.node),
                        | TypeMeaning::Family(_) => false,
                    })
        },
    )]
    fn stated_type(
        &mut self,
        site: Site,
        stated: TypeComponent<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match stated.meaning {
            TypeMeaning::Manifest(defined) | TypeMeaning::Instantiated { defined, .. }
                if self.cx().computation_members.contains(&defined.node) =>
            {
                Produced::CompType
            },
            TypeMeaning::Manifest(_)
            | TypeMeaning::Sealed
            | TypeMeaning::Instantiated { .. }
            | TypeMeaning::Family(_) => Produced::ValueType,
        };
        let _frame = self.require(site, produced)?;
        let plan = match stated.meaning {
            TypeMeaning::Manifest(defined) => Plan::Transparent(defined.node),
            TypeMeaning::Sealed | TypeMeaning::Instantiated { .. } => {
                let Some(atom) = self.cx().collected.slots.get(usize::from(stated.held))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::StatedType)));
                };
                if let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
                    && own <= stated.held
                {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: atom.name,
                        declared: atom.named.span,
                    });
                }
                match stated.meaning {
                    TypeMeaning::Instantiated { defined, instance } => {
                        Plan::Instantiated(instance, defined.node)
                    },
                    TypeMeaning::Sealed | TypeMeaning::Manifest(_) | TypeMeaning::Family(_) => {
                        Plan::Sealed(atom.constant)
                    },
                }
            },
            TypeMeaning::Family(_) => {
                return Err(site.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
            },
        };
        self.cx_mut().manifests.push((stated.held, site.at.node));
        if matches!(plan, Plan::Transparent(_) | Plan::Instantiated(..)) {
            let _fresh = self.cx_mut().stand_ins.insert(site.at.node);
        }
        self.plan(site, plan);

        Ok(())
    }

    /// The type component or type member `name` names at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inside a signature type, the latest of the type components
    ///   written before the type's own component that bears the name, and
    ///   nothing else; elsewhere, nothing where a binder answers the name, and
    ///   otherwise the type member [`Self::type_member_named`] answers.
    /// - provides: the one scope a stated type is named in, bare or applied.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when a walk outruns the
    ///   allowance; [`LoweringRefusal::ImportShadows`] when two imports write a
    ///   type member of the name, as [`Self::type_member_named`] refuses it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::ImportShadows`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a component named in a signature, a member named in a
    ///   body and a binder shadowing a member each resolve as stated.
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_is_named_only_after_it_is_written`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(stated)) => stated.name == name,
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    #[inline]
    pub fn stated_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>
    {
        let unresolved = Maybe::Absent(named::Absent::Unresolved);
        if let Some(&Maybe::Present(seen)) = self.cx().scopes.get(site.at.node) {
            return Ok(self
                .cx()
                .collected
                .structures
                .get(usize::from(seen.structure))
                .and_then(|structure| structure.types.get(.. seen.before))
                .and_then(|visible| visible.iter().rev().find(|stated| stated.name == name))
                .copied()
                .map_or(unresolved, Maybe::Present));
        }
        let cx = self.cx_mut();
        if let Maybe::Present(_) = cx.scope.resolve(site.reading.frame(), name, &mut cx.fuel)? {
            return Ok(unresolved);
        }

        self.type_member_named(site, name)
    }

    /// The member a path of names reaches from inside the modules enclosing
    /// the declaration that owns `site`: its head a module one of them
    /// declares, each link after it a module or a member the module before it
    /// exports.
    ///
    /// # Specification
    /// - requires: `links` are the path's selections, each its operand and its
    ///   member, the last link first, as [`Self::projection`] collects them.
    /// - ensures: the nearest module outward from the container of the
    ///   declaration owning `site` — its module, then each module enclosing it
    ///   — that declares a nested module named as `head` reads the path from
    ///   that nested module: each link but the last names a module the one
    ///   before it exports, and the last a member it exports, answered as the
    ///   slot the exporting module reads it at, its witness past a seal. A
    ///   nested module is a source-ordered member, so a use of one declared
    ///   after it answers its member and [`Self::select`] refuses it. A site at
    ///   a top level or owned by no declaration, a head no enclosing module
    ///   declares, and a link off a member that is not a module answer nothing.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; [`LoweringRefusal::UnknownMember`] at the first link the
    ///   module before it does not export, naming that module and the member;
    ///   the wrong-sort refusal for a path ending at a module, which is not a
    ///   value.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// The walk outward visits each enclosing container once and spends one
    /// step of the allowance on each; the walk down visits each link once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::projection`]'s nested module cases.
    /// - witness: `gandr-surface-lowering::tests::modules::a_nested_module_is_named_from_inside_its_enclosing_module_1106`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(member)) => self.cx().collected.slots.get(usize::from(member)).is_some(),
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    fn enclosed_member(
        &mut self,
        site: Site,
        head: Placed,
        links: &[(Placed, Placed)],
    ) -> Result<Maybe<SlotIndex, named::Absent>, LoweringRefusal<'source>>
    {
        let unresolved = Maybe::Absent(named::Absent::Unresolved);
        let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
        else {
            return Ok(unresolved);
        };
        let Some(slot) = self.cx().collected.slots.get(usize::from(own))
        else {
            return Ok(unresolved);
        };
        let mut container = slot.container;
        let name = self.cx().name_at(head);
        let nested = loop {
            self.cx_mut().fuel.spend()?;
            let Container::Module(module) = container
            else {
                return Ok(unresolved);
            };
            let Some(structure) = self.cx().collected.structures.get(usize::from(module))
            else {
                return Ok(unresolved);
            };
            let declared = structure.members.iter().find_map(|member| match *member {
                Member::Module(nested) => self
                    .cx()
                    .collected
                    .structures
                    .get(usize::from(nested))
                    .is_some_and(|held| held.name == name)
                    .then_some(nested),
                Member::Slot(_) => None,
            });
            if let Some(nested) = declared {
                break nested;
            }
            container = structure.container;
        };
        let (mut module, mut spelled) = (nested, name);
        for (place, &(_, selected)) in links.iter().rev().enumerate() {
            self.cx_mut().fuel.spend()?;
            let member = self.cx().name_at(selected);
            let Some(structure) = self.cx().collected.structures.get(usize::from(module))
            else {
                return Ok(unresolved);
            };
            let exported = structure
                .exports
                .iter()
                .copied()
                .find(|export| match *export {
                    Member::Slot(slot) => self
                        .cx()
                        .collected
                        .slots
                        .get(usize::from(slot))
                        .is_some_and(|held| held.name == member),
                    Member::Module(inner) => self
                        .cx()
                        .collected
                        .structures
                        .get(usize::from(inner))
                        .is_some_and(|held| held.name == member),
                });
            let last = place.saturating_add(1_usize) == links.len();
            match exported {
                Some(Member::Module(inner)) if !last => (module, spelled) = (inner, member),
                Some(Member::Slot(slot)) if last => {
                    return Ok(Maybe::Present(
                        self.cx().collected.exported_read(module, slot),
                    ));
                },
                Some(Member::Module(_)) => return Err(site.out(FragmentBoundary::WrongSort)),
                Some(Member::Slot(_)) => return Ok(unresolved),
                None => {
                    return Err(LoweringRefusal::UnknownMember {
                        span: selected.span,
                        module: spelled,
                        member,
                    });
                },
            }
        }

        Ok(unresolved)
    }

    /// The type member `name` names at `site`: one written before it in the
    /// module its declaration belongs to, in an enclosing one, at its source's
    /// top level, or at the top level of a source it imports unqualified.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the nearest container outward from the container of the
    ///   declaration owning `site` — its module, each module enclosing it, then
    ///   its source's top level — that declares a type member of the name,
    ///   written wholly before `site`, answers it, the last such of that
    ///   container; a flow's body is read as its domain, so a type component of
    ///   the flow's parameter answers the name there and the body's own members
    ///   do not; past the top level, the member its source's unqualified
    ///   imports answer, as [`Collected::imported_type_member`] reads them, the
    ///   import marked reached. A site no declaration owns, or a name no such
    ///   member has, answers nothing.
    /// - provides: the body scope of a type member.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; [`LoweringRefusal::ImportShadows`] when two imports write a
    ///   type member of the name, naming both.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::ImportShadows`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member's signature naming an earlier type member of
    ///   its own module, and one naming a member it precedes, separate the
    ///   scope from the module's whole body; a synonym an import writes, one
    ///   two imports write, and one only an import of the import writes,
    ///   separate the import fallback.
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_is_named_only_after_it_is_written`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_flow_reads_its_domain_s_sorts_by_name_3461`
    /// - witness: `gandr-surface-lowering::tests::modules::a_top_level_type_member_names_its_type_for_the_source_1834`
    /// - witness: `gandr-surface-lowering::tests::namespace::an_imported_top_level_type_member_names_its_type_1834`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(member)) => member.name == name
                && self.cx().collected.slots.get(usize::from(member.held)).is_some_and(|held| held.introduced_by.span.end() <= site.at.span.start()),
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    fn type_member_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>
    {
        let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let mut container = self.cx().collected.slots.get(usize::from(own)).map_or_else(
            || self.cx().collected.top(site.at.span.start()),
            |slot| slot.container,
        );
        loop {
            self.cx_mut().fuel.spend()?;
            // A flow's body reads its domain's sorts by name and never its
            // own, as it reads its values, so `type C = C ;` reads the
            // domain's `C`.
            if let Maybe::Present((parameter, outer)) = self.shared().domain_scope(container) {
                if let Some(&stated) = self
                    .cx()
                    .collected
                    .structures
                    .get(usize::from(parameter))
                    .and_then(|structure| structure.types.iter().find(|stated| stated.name == name))
                {
                    return Ok(Maybe::Present(stated));
                }
                container = outer;
                continue;
            }
            let written = self
                .cx()
                .collected
                .type_members_in(container)
                .filter(|member| {
                    member.name == name
                        && self
                            .cx()
                            .collected
                            .slots
                            .get(usize::from(member.held))
                            .is_some_and(|held| {
                                held.introduced_by.span.end() <= site.at.span.start()
                            })
                })
                .last();
            if let Some(&member) = written {
                return Ok(Maybe::Present(member));
            }
            let module = match container {
                Container::Module(module) => module,
                Container::TopLevel(source) => {
                    return match self.cx().collected.imported_type_member(source, name) {
                        Ok(Maybe::Present((member, import))) => {
                            self.cx_mut().collected.reach(import);
                            Ok(Maybe::Present(member))
                        },
                        Ok(Maybe::Absent(_)) => Ok(Maybe::Absent(named::Absent::Unresolved)),
                        Err(ambiguity) => Err(LoweringRefusal::ImportShadows {
                            span: site.at.span,
                            name,
                            import: ambiguity.import,
                            other: ambiguity.other,
                        }),
                    };
                },
            };
            let Some(structure) = self.cx().collected.structures.get(usize::from(module))
            else {
                return Ok(Maybe::Absent(named::Absent::Unresolved));
            };
            container = structure.container;
        }
    }

    /// Classify a qualified type reference `M.T`.
    ///
    /// # Specification
    /// - requires: `site` is a type path; `pieces` is its reading.
    /// - ensures: a chain of type paths whose head is a bare type name is one
    ///   path: inside a functor whose parameter the head names, a one-link path
    ///   is that parameter's type component, as [`Self::parameter_type`] reads
    ///   it; a one-link path whose head names a binder held at a theory's model
    ///   type is the carrier the model gives the sort the link names, as
    ///   `Models::carrier` reads it; otherwise it is resolved through the
    ///   outermost scope at the depth that binds it: a path ending at an
    ///   exported type component stands for what the component reads — the type
    ///   a manifest component or a type member names, the type member a
    ///   transparently ascribed abstract component reads, the atom an opaquely
    ///   ascribed one's abstract type declares, or an instance's manifest type;
    ///   a path ending at a data family a module exports stands for that
    ///   family, as [`Self::module_family`] reads it. The chain is walked by an
    ///   explicit loop, and its links are left unread. A one-link path whose
    ///   head is the alias of a path import reads the type the imported source
    ///   declares under the member, as a static application of it. A path whose
    ///   qualifier an import of a `std` module binds reads the former that
    ///   module homes under the member, as [`Self::applied_path`] reads it. A
    ///   path that writes an argument list after its type name, `M.F(Integer)`,
    ///   applies the member to it: a type family expands over the arguments and
    ///   a data family stands at them (#3051). A path that ends at a function a
    ///   module exports and writes an argument list calls that function, as
    ///   [`Self::applied_path`] reads it. Where a value is read, the path is
    ///   that call (#5213, #5383). Where a value is read, an unapplied path
    ///   that ends at a component that is no data family, a theory among them,
    ///   is the component's constant, as a projection reads it (#6174).
    /// - provides: the governed reading of a type path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a type a governing module or a
    ///   parameter does not export; [`LoweringRefusal::UnresolvedTypeHead`]
    ///   naming the head for a path no module governs;
    ///   [`LoweringRefusal::ProjectionFromApplication`] for a chain whose head
    ///   is an application of a functor; the wrong-sort refusal for a path
    ///   ending at a module, at a value component outside value position, and
    ///   outside value-type position; the forward-member refusal for a type
    ///   component declared at or after the referring declaration, so a type
    ///   always lowers before its readers; the arity refusal, naming the count
    ///   written, for an argument list a member does not take.
    /// - panics: none.
    ///
    /// # Errors
    /// The path's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to a sealed component, to a manifest one, to a
    ///   body type member, to a nested module's type, to an absent member, to a
    ///   value component and from an unbound head, each asserted as the exact
    ///   type or refusal; a path past a parameter's type, refused at that link;
    ///   a model binder's sort, read as its carrier; a module's family applied
    ///   through its name, read as its expansion, and refused at another count;
    ///   a module's function called where a value is read, read as the call; a
    ///   module's theory read where a value is read, as its constant.
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `gandr-surface-lowering::tests::modules::an_unbound_type_path_is_refused_by_name`
    /// - witness: `gandr-surface-lowering::tests::modules::opaque_ascription_seals`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_parameter_is_read_only_inside_its_functor`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_model_binder_s_carrier_is_its_projected_sort_2131`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_where_a_value_is_read_5383`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_theory_is_a_value_in_a_type_6174`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Transparent(_) | Plan::Sealed(_) | Plan::Instantiated(..) | Plan::Decode(..) | Plan::Unquote(..) | Plan::Reapplied(..) | Plan::Carrier(..) | Plan::FixedCarrier(..) | Plan::Data(..) | Plan::Expansion(..) | Plan::StaticApplication(..) | Plan::Called(..) | Plan::Forced(_) | Plan::Former(..) | Plan::Constant(_)))
                )
        },
    )]
    fn type_path(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let start = self.cx().operands.entries().len();
        let read = path_arguments(
            site,
            &pieces.pieces,
            site.at.span,
            &mut self.cx_mut().operands,
        )
        .and_then(|lists| self.applied_path(site, pieces, lists));
        if read.is_err() {
            self.cx_mut().operands.truncate(At::from(start));
        }
        read
    }

    /// Classify the qualified type reference `M.T` at `site`, applied to the
    /// arguments `applied` holds in the operand store when it writes them,
    /// `M.F(A)`, and to those `again` holds when it applies the result once
    /// more, `M.f(a)(b)`.
    ///
    /// # Specification
    /// - requires: `site` is a type path; `pieces` is its reading; `applied` is
    ///   the stretch of its first argument list and `again` of its second, each
    ///   when it writes one.
    /// - ensures: as [`Self::type_path`], each reading of an unapplied path the
    ///   same; an applied path ending at a type family a module exports expands
    ///   it over the arguments, as `Models::expansion` reads it, and one ending
    ///   at a data family a module exports, or at the type an import's alias
    ///   names, stands applied to them. A path whose qualifier an import of a
    ///   `std` module binds and whose member that module homes as a former,
    ///   `l.List(A)`, stands as that former applied to its one argument, as
    ///   [`Self::qualified_former`] reads it. A path ending at a value name a
    ///   module or an import's alias exports, `Standard.ext(a, b)`, is the call
    ///   [`Self::call_resolved`] reads (#5213).
    /// - fails: as [`Self::type_path`]; the arity refusal for an applied path
    ///   ending at anything but a family, an imported type or a function, for a
    ///   homed former written at any count but one, and for a second list after
    ///   anything but a function.
    /// - panics: none.
    /// - executable: none — [`Self::type_path`] states the plans.
    ///
    /// # Errors
    /// The path's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::type_path`]; `M.F(Integer)` expands to the
    ///   family's type, `M.Box(Integer)` stands as the data family, and
    ///   `M.T(Integer)` over an unparameterised member is refused by its arity;
    ///   `std.list.List(Integer)` and `l.List(Integer)` stand as the native
    ///   list; `M.f(a)`, `M.f()` and `M.f(a)(b)` stand as the calls.
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
    /// - witness: `gandr-surface-lowering::lower::tests::a_homed_former_reads_through_its_import_s_qualifier_4862`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
    fn applied_path(
        &mut self,
        site: Site,
        pieces: &Pieces,
        (applied, again): (Option<Stretch>, Option<Stretch>),
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // Each link is the module a name is selected from and the name, from
        // the outermost; a link through nested modules, `Sealed.inner.T` or
        // `a.b.c.T`, is one per module and one for the type.
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (target, nested, member) = Context::type_link(site, &pieces.pieces, site.at.span)?;
        F::linked(&mut links, target, nested, member);
        // A link that ends at a value name calls a function (#5213).
        let valued = matches!(
            pieces.pieces.get(nested.len().saturating_add(2_usize)),
            Some(&Piece::Tile {
                label: TileName::TYPE_VARIABLE,
                ..
            })
        );
        if !valued {
            unapplied(site, again)?;
        }
        let headed = match self.cx().tree.node(target.node) {
            Some(node) => matches!(shape_of(self.cx().pbg, node)?, Shape::Form {
                former: Former::TypeHead,
                ..
            }),
            None => false,
        };
        // The qualifier is the head alone, `g.Mood`, or the head and the
        // modules after it, `text.greet.Mood`, when an import binds that path.
        let qualifier = match links.first() {
            Some(&(module, _)) if !nested.is_empty() => {
                ByteSpan::new(target.span.start(), module.span.end())
                    .ok()
                    .map(|span| Placed { span, ..target })
            },
            Some(_) | None => Some(target),
        };
        if headed
            && !valued
            && let Some(qualifier) = qualifier
            && let Some(former) = self.qualified_former(site, qualifier, member)
        {
            let count =
                applied.map_or(0_usize, |written| written.end.saturating_sub(written.start));
            let argument = applied
                .and_then(|written| self.cx().operands.entries().get(written.start).copied());
            return match (argument, count) {
                (Some(argument), 1_usize) => self.apply_former(site, former, argument),
                (Some(_) | None, _) => {
                    Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))))
                },
            };
        }
        if headed
            && let Some(qualifier) = qualifier
            && let Maybe::Present(resolved) = self.aliased_member(site, qualifier, member)?
        {
            return self.call_resolved(site, resolved, applied, again);
        }
        let head = self.path_head(site, target, &mut links)?;
        if let Some(&(_, first)) = links.last()
            && self.parameter_type(site, head, first, functor::Deeper(links.len() > 1_usize))?
                == functor::Read::Planned
        {
            return unapplied(site, applied);
        }
        if let &[(_, member)] = links.as_slice()
            && Models::new(self.host()).carrier(site, head, member)? == arity::Planned(true)
        {
            return unapplied(site, applied);
        }
        let path = self.shared().path_named(head, &links);
        let cx = self.cx_mut();
        cx.collected.reach_declaring(
            cx.collected.unit.source_at(site.at.span.start()),
            cx.name_at(head),
        );
        self.see_module(site, self.cx().name_at(head));
        match self.cx().recognition.resolve_path(&path) {
            PathResolution::Complete(Recognized::ModuleType) => {
                self.module_type(site, &path, member, applied)
            },
            PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.cx().name_at(prefix),
                    member: self.cx().name_at(selected),
                })
            },
            PathResolution::Ungoverned => Err(LoweringRefusal::UnresolvedTypeHead {
                span: head.span,
                head: head.span,
                name: self.cx().name_at(head),
                arity: HeadArity::Nullary,
            }),
            PathResolution::Complete(Recognized::ModuleComponent) if valued => {
                self.module_call(site, &path, (head, member), applied, again)
            },
            PathResolution::Complete(Recognized::ModuleComponent) => {
                self.module_family(site, &path, (head, member), applied)
            },
            PathResolution::Complete(_) => Err(site.out(FragmentBoundary::WrongSort)),
        }
    }

    /// Read the module's type component at `path`, the one `member` names, as
    /// its stated type, applied to the arguments `applied` holds when the path
    /// writes them.
    ///
    /// # Specification
    /// - requires: `path` resolves to a module's type component; `applied` is a
    ///   stretch of the operand store when present.
    /// - ensures: the stated type, read at `site`'s own reading, when the
    ///   component is declared strictly before the declaration `site` belongs
    ///   to; applied, a type family's expansion over the arguments, as
    ///   `Models::expansion` reads it.
    /// - provides: a type path's reading, in a type and where a value is read.
    /// - fails: yields the unadmitted refusal for a component the exports do
    ///   not hold, and [`LoweringRefusal::ForwardMemberReference`] for one
    ///   declared at or after the referring declaration; the arity refusal for
    ///   arguments after a component that is no type family, and the family's
    ///   own refusals.
    /// - panics: none.
    /// - executable: none — the plan is the stated type's, which
    ///   [`Self::stated_type`] makes, or the expansion's, and each one's own
    ///   predicate checks it.
    ///
    /// # Errors
    /// The component's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a qualified type in a type and as an argument lower
    ///   to the code the type's unqualified alias lowers to; a module's family
    ///   applied through its name expands as it does applied bare.
    /// - witness: `gandr-surface-lowering::lower::tests::a_qualified_type_argument_is_the_code_its_alias_is_1126`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
    fn module_type(
        &mut self,
        site: Site,
        path: &NamePath,
        member: Placed,
        applied: Option<Stretch>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(&stated) = self.cx().exported_types.get(path)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
        };
        if let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
            && own <= stated.held
            && let Some(held) = self.cx().collected.slots.get(usize::from(stated.held))
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name: self.cx().name_at(member),
                declared: held.named.span,
            });
        }
        match (applied, stated.meaning) {
            (None, _) => self.stated_type(site, stated),
            (Some(applied), TypeMeaning::Family(family)) => {
                let _first = self
                    .cx_mut()
                    .expansions
                    .insert(site.at.node, (site.at.span, site.reading.frame()));
                Models::new(self.host()).expansion(site, family, stated.held, applied)
            },
            (
                Some(_),
                TypeMeaning::Manifest(_) | TypeMeaning::Sealed | TypeMeaning::Instantiated { .. },
            ) => unapplied(site, applied),
        }
    }

    /// Read the module component at `path`, the one the link's `member` names
    /// under its `head`, as the data family it declares, applied to the
    /// arguments `applied` holds when the path writes them.
    ///
    /// # Specification
    /// - requires: `path` resolves to a module's value component; `applied` is
    ///   a stretch of the operand store when present.
    /// - ensures: the family over the arguments, none when the path writes
    ///   none, as `Native::family` reads it, when the component is a data
    ///   family declared strictly before the declaration `site` belongs to.
    ///   Where a value is read, an unapplied component that is no data family
    ///   is its value, as [`Self::component_value`] reads it (#6174).
    /// - provides: a type path's reading of a family a module body declares.
    /// - fails: the wrong-sort refusal for a component that is no data family,
    ///   except as a value; [`LoweringRefusal::ForwardMemberReference`] for one
    ///   declared at or after the referring declaration; the export refusal of
    ///   a component its source keeps private; the family's own refusals.
    /// - panics: none.
    /// - executable: none — the plan is the family's, which `Native::family`
    ///   makes and its own predicate checks.
    ///
    /// # Errors
    /// The component's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `M.Box` in a declared type and in a parameter's type
    ///   lowers to the family a top-level `Box` lowers to, and `M.Box(Integer)`
    ///   to the family at `Integer`.
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_member_family_is_named_through_the_module_4298`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_theory_is_a_value_in_a_type_6174`
    fn module_family(
        &mut self,
        site: Site,
        path: &NamePath,
        (head, member): (Placed, Placed),
        applied: Option<Stretch>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(&exported) = self.cx().exported.get(path)
        else {
            return Err(site.out(FragmentBoundary::WrongSort));
        };
        let Some(held) = self.cx().collected.slots.get(usize::from(exported))
        else {
            return Err(site.out(FragmentBoundary::WrongSort));
        };
        let (constant, declared) = (held.constant, held.named.span);
        let Maybe::Present(arity) = NativeRef::over(self.cx()).data_family(constant)
        else {
            // A component that is no family, as a theory's presentation, is
            // its value where a value is read (#6174).
            if applied.is_none() && matches!(site.reading, Reading::Value(_)) {
                return self.component_value(site, exported, head, Some(member));
            }
            return Err(site.out(FragmentBoundary::WrongSort));
        };
        if let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
            && own <= exported
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name: self.cx().name_at(member),
                declared,
            });
        }
        self.shared()
            .exported_across(site, self.cx().name_at(head), exported)?;
        self.resolved(member.span, Resolved::Declaration {
            constant,
            declared: Maybe::Absent(binder_type::Absent::Untyped),
        });
        let none = Stretch {
            start: self.cx().operands.entries().len(),
            end: self.cx().operands.entries().len(),
        };
        Native::new(self.host()).family(site, constant, arity, applied.unwrap_or(none))
    }

    /// Read the module component at the slot `exported`, which a path through
    /// the module `head` selects, as its value: the declaration the slot holds.
    ///
    /// # Specification
    /// - requires: `exported` is the slot of a value component that a module
    ///   exports, and `member` is the name that selects it, when the path
    ///   writes one.
    /// - ensures: the selection of the slot's declaration, as [`Self::select`]
    ///   plans it, with the use at `member` resolved to that declaration.
    /// - provides: the value half of a module's path, for a projection and for
    ///   a type path read where a value is expected (#6174).
    /// - fails: [`LoweringRefusal::GenericMisplaced`] for the prelude's
    ///   derivation; the export refusal of a component its source keeps
    ///   private; the refusals of [`Self::select`].
    /// - panics: none.
    /// - executable: none — [`Self::select`] states the plan.
    ///
    /// # Errors
    /// The component's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `M.x` in a body and `Gandr.Package` as the argument
    ///   of a type each read as the declaration that the module exports.
    /// - witness: `gandr-surface-lowering::tests::modules::a_backward_member_reference_resolves`
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_theory_is_a_value_in_a_type_6174`
    fn component_value(
        &mut self,
        site: Site,
        exported: SlotIndex,
        head: Placed,
        member: Option<Placed>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // The prelude's derivation is no value: it stands only as the head of
        // a definition's whole body (`lower::generic`).
        if self.cx().generic == Some(exported) {
            return Err(LoweringRefusal::GenericMisplaced { span: site.at.span });
        }
        self.shared()
            .exported_across(site, self.cx().name_at(head), exported)?;
        self.select(site, exported)?;
        if let Some(member) = member
            && let Some(entry) = self.cx().collected.slots.get(usize::from(exported))
        {
            self.resolved(member.span, Resolved::Declaration {
                constant: entry.constant,
                declared: Maybe::Absent(binder_type::Absent::Untyped),
            });
        }
        Ok(())
    }

    /// Read the module component at `path`, the function the link's `member`
    /// names under its `head`, as the call the type path writes: applied to the
    /// arguments `applied` holds, and its result to those `again` holds when
    /// the path writes a second list (#5213).
    ///
    /// # Specification
    /// - requires: `path` resolves to a module's value component; `applied` and
    ///   `again` are stretches of the operand store when present.
    /// - ensures: the call [`Self::call_resolved`] reads of the component's
    ///   declaration, its written type the one its signature states, when the
    ///   component is declared strictly before the declaration `site` belongs
    ///   to and its source exports it.
    /// - provides: a type path's reading of a function a module body declares,
    ///   as the call form reads the same function named bare.
    /// - fails: the wrong-sort refusal for a path no export holds;
    ///   [`LoweringRefusal::ForwardMemberReference`] for a component declared
    ///   at or after the referring declaration; the export refusal of a
    ///   component its source keeps private; the call's own refusals.
    /// - panics: none.
    /// - executable: none — the plan is the call's, which
    ///   [`Self::listed_application`] makes and its own predicate checks.
    ///
    /// # Errors
    /// The component's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `M.f(a)`, `M.f()` and `M.f(a)(b)` in a declared type
    ///   lower to the decode of the call the bare `f` gives.
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
    fn module_call(
        &mut self,
        site: Site,
        path: &NamePath,
        (head, member): (Placed, Placed),
        applied: Option<Stretch>,
        again: Option<Stretch>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(&exported) = self.cx().exported.get(path)
        else {
            return Err(site.out(FragmentBoundary::WrongSort));
        };
        let Some(held) = self.cx().collected.slots.get(usize::from(exported))
        else {
            return Err(site.out(FragmentBoundary::WrongSort));
        };
        let (constant, named) = (held.constant, held.named.span);
        let declared = match held.signature {
            Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) => Maybe::Present(written.node),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
        };
        if let Maybe::Present(own) = self.cx().collected.owner_of(site.at.node)
            && own <= exported
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name: self.cx().name_at(member),
                declared: named,
            });
        }
        self.shared()
            .exported_across(site, self.cx().name_at(head), exported)?;
        let resolved = Resolved::Declaration { constant, declared };
        self.resolved(member.span, resolved);
        self.call_resolved(site, resolved, applied, again)
    }

    /// The head of the chain of type paths whose innermost operand is
    /// `target`, each link it walks pushed onto `links`, from the outermost.
    ///
    /// # Specification
    /// - requires: `target` is the operand of a type path at `site`, and
    ///   `links` holds that path's own links.
    /// - ensures: the bare type name the chain bottoms out at; each type path
    ///   on the way adds its links, the innermost last.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; the unadmitted projection refusal for a chain ending at
    ///   another form, for a link that writes an argument list, and for an
    ///   application of a functor once
    ///   [`Self::refuse_applied`](crate::lower::ExpressionsRef::refuse_applied)
    ///   reads it; a malformed link's refusal.
    /// - panics: none.
    /// - executable: none — the head is read off the syntax tree, which a
    ///   predicate could check only by repeating the walk.
    ///
    /// # Errors
    /// The chain's refusal.
    ///
    /// # Termination
    /// Each turn spends one unit of the allowance and steps to the operand of
    /// the type path it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::type_path`].
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `gandr-surface-lowering::lower::session::tests::a_parameter_at_a_named_session_type_is_placed`
    #[inline]
    pub fn path_head(
        &mut self,
        site: Site,
        mut target: Placed,
        links: &mut Vec<(Placed, Placed)>,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        let mut chain = Pieces::new();
        loop {
            self.cx_mut().fuel.spend()?;
            let Some(node) = self.cx().tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
            };
            match shape_of(self.cx().pbg, node)? {
                Shape::Form {
                    former: Former::TypePath,
                    ..
                } => {
                    read_pieces(self.cx().pbg, self.cx().tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(repaired.refusal(site.name));
                    }
                    // A link applied to arguments, `M.F(A).G`, selects out of
                    // an application, which no module is.
                    if chain.pieces.iter().any(|piece| {
                        matches!(*piece, Piece::Tile {
                            label: TileName::PAREN_OPEN,
                            ..
                        })
                    }) {
                        return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                    }
                    let (inner, nested, selected) =
                        Context::type_link(site, &chain.pieces, target.span)?;
                    F::linked(links, inner, nested, selected);
                    target = inner;
                },
                Shape::Form {
                    former: Former::TypeHead,
                    ..
                } => return Ok(target),
                Shape::Form {
                    former: Former::TypeApplication,
                    ..
                } => {
                    self.shared().refuse_applied(target, &mut chain)?;
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                },
                Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection)));
                },
            }
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The name path the head `head` and the links `links` spell, from the
    /// head, as [`Self::path_head`](crate::lower::Expressions::path_head)
    /// collects them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path_named(
        &self,
        head: Placed,
        links: &[(Placed, Placed)],
    ) -> NamePath
    {
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.cx().text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.cx().text_at(selected).as_ref()));
        }
        NamePath::from(segments)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify a universe, `Type[s, l]`.
    ///
    /// # Specification
    /// - requires: `site` is a universe in type position, or in value position
    ///   where it is quoted.
    /// - ensures: a universe standing as a value type is planned at the sort
    ///   and level written, the value sort and the fuss-free level supplied for
    ///   whichever is left off.
    /// - provides: the universe former of the fragment.
    /// - fails: yields the wrong-sort refusal where its position reads no value
    ///   type, a misplaced-tile fault for a bracket out of shape, and the
    ///   unadmitted refusal for a level the core's level width holds without
    ///   its successor.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bare spelling, a sort alone and a sort with a
    ///   level at each sort, each asserted as the exact core universe.
    /// - witness: `gandr-surface-lowering::lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&Plan::Universe(_))
                )
        },
    )]
    fn universe(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let universe = self.shared().universe_of(site, &mut cursor)?;

        self.plan(site, Plan::Universe(universe));

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The universe a universe form's pieces spell.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the form's `Type` tile.
    /// - ensures: the sort `+` or `-` and the level numeral written, the value
    ///   sort and level zero for whichever is left off.
    /// - provides: the one reading of a universe's spelling, shared by the
    ///   universe former and the decode that reads a binder's written type.
    /// - fails: a misplaced-tile fault for a bracket out of shape;
    ///   [`LoweringRefusal::NoUniverseAbove`] for a level numeral wider than a
    ///   level constant or spelling the greatest one, whose universe no
    ///   universe stands above.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the supported spellings consume the complete form and
    ///   the spelling without brackets denotes the fuss-free universe. Explicit
    ///   sort and level values are checked by the same bounded spelling table.
    /// - witness: `gandr-surface-lowering::lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        captures: plain = {
            let mut input = cursor.clone();
            let _keyword = input.tile(TileName::UNIVERSE);
            matches!(input.at(TileName::BRACKET_OPEN), Maybe::Absent(_))
        },
        ensures: |ret| {
            ret.as_ref().map_or(true, |universe| {
                matches!(cursor.peek(), Maybe::Absent(_))
                    && (!plain || *universe == Universe::FUSS_FREE)
            })
        },
    )]
    fn universe_of(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let universe = self.universe_tiles(site, cursor)?;
        exhausted(site, cursor)?;

        Ok(universe)
    }

    /// The universe the `Type` tile at `cursor` and the bracket after it spell,
    /// the cursor left past them.
    ///
    /// # Specification
    /// - requires: `cursor` stands at a `Type` tile.
    /// - ensures: as [`Cursor::universe`], the cursor left past the universe's
    ///   last tile rather than required at the form's end. A misplaced tile is
    ///   refused as `MisplacedTile`, and a level with no universe above it as
    ///   `NoUniverseAbove` at its numeral.
    /// - provides: the universe a path type's carrier spells inline.
    /// - fails: as [`Self::universe_of`].
    /// - panics: none.
    /// - executable: none — where the cursor stands after the call has no
    ///   observer but the tiles the caller reads next; [`Self::universe_of`]
    ///   holds the whole form to its end.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::universe_of`], and a path type at a
    ///   levelled universe; a level past the constants or at the greatest,
    ///   refused at its numeral.
    /// - witness: `gandr-surface-lowering::lower::tests::every_universe_spelling_lowers_to_its_universe`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_path_at_a_universe_reads_its_endpoints_as_types_402`
    /// - witness: `gandr-surface-lowering::lower::tests::a_universe_level_at_or_past_the_greatest_has_none_above_2653`
    #[inline]
    pub fn universe_tiles(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        cursor
            .universe(self.cx().tree)
            .map_err(|misspelt| match misspelt {
                Misspelt::Misplaced(span) => site.fault(span, FormFault::MisplacedTile),
                Misspelt::NoneAbove(numeral) => LoweringRefusal::NoUniverseAbove {
                    span: numeral.span,
                    level: self.cx().name_at(numeral),
                },
            })
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The universe a code of the type at `declared`, applied statically to
    /// `applied` arguments, decodes in; `fallback` where the type does not
    /// say.
    ///
    /// # Specification
    /// - requires: `declared`, when present, is a node of the tree.
    /// - ensures: read through any grouping parentheses, each of the first
    ///   `applied` arrows of the type steps to its codomain, and the universe
    ///   form the walk then reaches is the universe it spells; `fallback` for
    ///   an absent type, for a walk that meets any other form or an arrow too
    ///   few or too many, and for a universe out of shape, whose own reading
    ///   reports it.
    /// - provides: the sort and level a decode of a binder, a declaration or a
    ///   static application of either is minted at.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to an
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at a sorted, levelled universe
    ///   inside a grouping, a declaration signed at one, an operator's codomain
    ///   reached through one static arrow, and an unwritten type at each sort
    ///   of position, each observed through the decode it mints; an operator
    ///   whose codomain does not fit the application decoding where it stands.
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_its_operator_does_not_fit_decodes_where_it_stands`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(declared, Maybe::Present(_))
                || ret.as_ref().is_ok_and(|universe| *universe == fallback)
        },
    )]
    fn written_universe(
        &mut self,
        declared: Maybe<NodeIndex, binder_type::Absent>,
        applied: OperandCount,
        fallback: Universe,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let Maybe::Present(mut position) = declared
        else {
            return Ok(fallback);
        };
        let mut remaining = usize::from(applied);
        loop {
            self.cx_mut().fuel.spend()?;
            let Some(node) = self.cx().tree.node(position)
            else {
                return Ok(fallback);
            };
            let Ok(Shape::Form { name, former }) = shape_of(self.cx().pbg, node)
            else {
                return Ok(fallback);
            };
            let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
            let read = read_pieces(self.cx().pbg, self.cx().tree, position, &mut scratch);
            let site = Site {
                at: Placed::of(position, node),
                name,
                reading: Reading::ValueType(Frame::Outermost),
            };
            let mut cursor = Cursor::new(&scratch.pieces, site.at.span);
            let step = match (read, former) {
                (Ok(()), Former::Universe) if remaining == 0_usize => ControlFlow::Break(
                    self.shared()
                        .universe_of(site, &mut cursor)
                        .unwrap_or(fallback),
                ),
                (Ok(()), Former::ParenthesizedType) => {
                    let _open = cursor.tile(TileName::PAREN_OPEN);
                    match cursor.operands() {
                        Run::One(operand) => ControlFlow::Continue(operand.node),
                        Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                (Ok(()), Former::ArrowType) if remaining > 0_usize => {
                    remaining = remaining.saturating_sub(1_usize);
                    let _domain = cursor.operands();
                    let _arrow = cursor.tile(TileName::ARROW);
                    match cursor.operands() {
                        Run::One(operand) => ControlFlow::Continue(operand.node),
                        Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                _ => ControlFlow::Break(fallback),
            };
            self.cx_mut().scratch = scratch;
            match step {
                ControlFlow::Continue(operand) => position = operand,
                ControlFlow::Break(universe) => return Ok(universe),
            }
        }
    }

    /// Classify a type head applied to arguments, `Foo(A)`.
    ///
    /// # Specification
    /// - requires: `site` is a type application in type position, or in value
    ///   position where a type is quoted or a constructor applied.
    /// - ensures: a spine whose head is a path or bridge type that supplies its
    ///   carrier, `Path[.A = C] a b`, is that type over the spine's operands,
    ///   as [`Identities::carried_path`] plans it. An application standing
    ///   where a value is read — an argument of a type-position call — whose
    ///   head names a constructor of a data family declared strictly earlier
    ///   stands as that constructor applied to the arguments, as
    ///   `Native::construct` plans it. Otherwise a head naming a type family,
    ///   as a component or a member, expands to the family's type over the
    ///   arguments; a head naming a codata family stands as that family's
    ///   computation type over the arguments; a head a binder or an earlier
    ///   declaration answers is read as the static application of that code to
    ///   the arguments, left to right, or, holding a function where a value is
    ///   read, as its call; any other head is the type former
    ///   [`Self::applied_head`] plans.
    /// - provides: the applied half of type-head resolution.
    /// - fails: yields the unresolved-head refusal for a head nothing answers
    ///   and no former takes at the arity it was written with, the wrong-sort
    ///   refusal for a former or an application whose sort does not suit the
    ///   position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a former's head, a head no former takes, a head
    ///   written at two arguments, an operator a declaration and a binder name,
    ///   and a constructor applied in a type-position call's argument, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal; a forward member applied, refused at its head; a
    ///   carried path head over its two endpoints.
    /// - witness: `gandr-surface-lowering::lower::tests::u_and_f_are_names`
    /// - witness: `gandr-surface-lowering::lower::tests::an_applied_head_no_former_answers_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_run_bound_type_and_a_constructor_argument_stand_in_a_type`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `gandr-surface-lowering::lower::tests::a_forward_member_applied_as_a_type_is_refused_at_its_head`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_carried_path_head_takes_its_endpoints_by_juxtaposition_6121`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Former(..) | Plan::Decode(..) | Plan::Unquote(..) | Plan::Reapplied(..) | Plan::StaticApplication(..) | Plan::Called(..) | Plan::Forced(_) | Plan::Data(..) | Plan::Codata(..) | Plan::Expansion(..) | Plan::Path(..) | Plan::Flow(..) | Plan::Relation(..) | Plan::Stack(..) | Plan::Bundle(_) | Plan::Constructor(_)))
                )
        },
    )]
    fn type_application(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // A path or bridge type that supplies its carrier heads the spine
        // that applies it to its endpoints, `Path[.A = C] a b`.
        if let Maybe::Present(Piece::Operand(head)) = cursor.peek()
            && let Some(named) = IdentitiesRef::new(self.host_ref()).carried_head(head)?
        {
            let (name, relating) = named;
            return Identities::new(self.host()).carried_path(site, (name, head), cursor, relating);
        }
        let Maybe::Present(head) = cursor.type_head()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let name = self.cx().name_at(head);
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            return Native::new(self.host()).staged_unquote(site, name, cursor);
        }
        let start = self.cx().operands.entries().len();
        // A second list applies the call's result once more, `f(a)(b)`
        // (#5213); only a function's call takes it, and every other head
        // refuses it.
        let lists = argument_lists(site, &mut cursor, &mut self.cx_mut().operands);
        let again = lists.as_ref().ok().copied().flatten();
        let read = lists.map(|_| ());
        let applied = Stretch {
            start,
            end: again.map_or_else(|| self.cx().operands.entries().len(), |again| again.start),
        };
        let alone = |again: Option<Stretch>| {
            again.map_or(Ok(()), |again| {
                Err(site.out(FragmentBoundary::Arity(OperandCount::from(
                    again.end.saturating_sub(again.start),
                ))))
            })
        };
        // The sorts a manifest type closing the application fixes, read after
        // `Model` alone: any other head that answers it is refused at the
        // first sort.
        let manifests = self
            .cx()
            .fixed_sorts
            .get(&site.at.node)
            .cloned()
            .unwrap_or_default();
        let unmanifest = manifests
            .first()
            .map(|&(sort, _)| site.fault(sort.span, FormFault::MisplacedTile));
        if let (Ok(()), Reading::Value(_)) = (read, site.reading)
            && let Maybe::Present(constructor) = Native::new(self.host())
                .named_constructor(site, name)
                .inspect_err(|_| self.cx_mut().operands.truncate(At::from(start)))?
        {
            if let Some(refusal) = unmanifest.or_else(|| alone(again).err()) {
                self.cx_mut().operands.truncate(At::from(start));
                return Err(refusal);
            }
            return Native::new(self.host()).construct(site, constructor, applied);
        }
        match read.and_then(|()| self.stated_named(site, name)) {
            Ok(Maybe::Present(TypeComponent {
                meaning: TypeMeaning::Family(family),
                held,
                ..
            })) => {
                if let Some(refusal) = unmanifest.or_else(|| alone(again).err()) {
                    self.cx_mut().operands.truncate(At::from(start));
                    return Err(refusal);
                }
                let _first = self
                    .cx_mut()
                    .expansions
                    .insert(site.at.node, (site.at.span, site.reading.frame()));
                return Models::new(self.host()).expansion(site, family, held, applied);
            },
            Ok(Maybe::Present(_) | Maybe::Absent(_)) => {},
            Err(refusal) => {
                self.cx_mut().operands.truncate(At::from(start));
                return Err(refusal);
            },
        }
        let resolved = read.and_then(|()| {
            let named = Site { at: head, ..site };
            self.resolve_name(named, site.reading.frame(), name)
        });
        match resolved {
            Ok(Maybe::Present(resolved)) => {
                if let Some(refusal) = unmanifest {
                    self.cx_mut().operands.truncate(At::from(start));
                    return Err(refusal);
                }
                self.resolved(head.span, resolved);
                return self.listed_application(
                    site,
                    resolved,
                    applied,
                    again.map_or(Lists::Called, Lists::Again),
                );
            },
            Ok(Maybe::Absent(named::Absent::Unresolved)) => {},
            Err(refusal) => {
                self.cx_mut().operands.truncate(At::from(start));
                return Err(refusal);
            },
        }

        if let Err(refusal) = alone(again) {
            self.cx_mut().operands.truncate(At::from(start));
            return Err(refusal);
        }
        self.applied_head(site, head, name, applied, &manifests)
    }

    /// Classify the type former `name`, written at `head` and applied to the
    /// operands `written` holds in the operand store and closed by the
    /// manifest sorts `manifests`, which nothing the scope binds answers.
    ///
    /// # Specification
    /// - requires: `written` is the arguments the head was written with, left
    ///   to right, and the last the store holds; `manifests` is each manifest
    ///   sort's name beside the type it is, in written order.
    /// - ensures: the arguments leave the store; a head named `Path` or
    ///   `Bridge` and applied to two arguments is the path or bridge type
    ///   [`Identities::written_path`] plans, one named `Flow` and applied to
    ///   two the directed identity type [`Identities::flow_type`] plans, one
    ///   named `Stack` and applied to two the continuation type
    ///   [`Self::stack_type`] plans, one named `Iso` and applied to two the
    ///   quasi-inverse `A ≅ B` [`Identities::relation_of`] plans, one named
    ///   `Model` and applied to one the bundled record `Models::model_type`
    ///   plans with its manifest sorts, one named `Terms` and applied to one
    ///   the theory's terms `Native::terms_type` plans; any other head applied
    ///   to one argument resolves against the unary table, stands at the sort
    ///   its former produces, reads its argument at the sort the former takes,
    ///   and is planned over it.
    /// - provides: the one table of type formers written as an application, in
    ///   a type and where a value is read.
    /// - fails: yields the unresolved-head refusal for a head no former takes
    ///   at the arity it was written with, marking the whole application when
    ///   the head spells a former and the head alone otherwise; the
    ///   positional-carrier fault at a `Path`, `Bridge` or `Flow` head applied
    ///   to three arguments; the wrong-sort refusal for a former whose sort
    ///   does not suit the position; and a misplaced tile at the first manifest
    ///   sort after any head but `Model`.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a former's head, a head no former takes, a head
    ///   written at two arguments, a path type and a list type written as calls
    ///   where a value is read, and `Iso(A, B)` beside `A ≅ B`, each asserted
    ///   as the exact core node read back out of the arena or the exact
    ///   refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::u_and_f_are_names`
    /// - witness: `gandr-surface-lowering::lower::tests::an_applied_head_no_former_answers_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::an_omitted_carrier_is_a_nominated_hole_4932`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_carrier_written_first_is_refused_5024`
    #[spec(
        ensures: |ret| {
            self.cx().operands.entries().len() == written.start
                && (ret.is_err()
                    || matches!(
                        self.cx().plans.get(site.at.node),
                        Some(&(Plan::Former(..) | Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..) | Plan::Relation(..) | Plan::Bundle(_) | Plan::Data(..)))
                    ))
        },
    )]
    fn applied_head(
        &mut self,
        site: Site,
        head: Placed,
        name: SurfaceName<'source>,
        written: Stretch,
        manifests: &[(Placed, Placed)],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let start = written.start;
        let count = written.end.saturating_sub(start);
        let first = self.cx().operands.entries().get(start).copied();
        let written_first = count == 3_usize;
        let pair = self
            .cx()
            .operands
            .entries()
            .get(start .. written.end)
            .and_then(|operands| <[NodeIndex; 2]>::try_from(operands).ok());
        self.cx_mut().operands.truncate(At::from(start));
        if let (Some(argument), 1_usize) = (first, count)
            && name.as_ref() == MODEL
        {
            return Models::new(self.host()).model_type(site, argument, manifests);
        }
        if let Some(&(sort, _)) = manifests.first() {
            return Err(site.fault(sort.span, FormFault::MisplacedTile));
        }
        if let (Some(argument), 1_usize) = (first, count)
            && name.as_ref() == TERMS
        {
            return Native::new(self.host()).terms_type(site, argument);
        }
        let path_shaped = [TileName::PATH, TileName::BRIDGE, TileName::FLOW_TYPE]
            .into_iter()
            .find(|shaped| name.as_ref() == shaped.as_ref());
        if let (Some(shaped), true) = (path_shaped, written_first) {
            return Err(site.fault(head.span, FormFault::PositionalCarrier(shaped)));
        }
        if let Some(written) = pair
            && let Some(relating) = [Relating::Path, Relating::Bridge]
                .into_iter()
                .find(|relating| name.as_ref() == relating.head().as_ref())
        {
            return Identities::new(self.host()).written_path(site, written, relating);
        }
        if let Some(written) = pair
            && name.as_ref() == identity::FLOW
        {
            return Identities::new(self.host()).flow_type(site, written);
        }
        if let Some(written) = pair
            && name.as_ref() == STACK
        {
            return self.stack_type(site, written);
        }
        if let Some(written) = pair
            && name.as_ref() == identity::ISO
        {
            return Identities::new(self.host()).relation_of(site, Relation::Isomorphism, written);
        }
        let former = self.cx().former(name);
        // The refusal marks the application it judged, head and arguments,
        // and names the head inside it. A near miss of a tile can turn
        // another form into this application, so the mistake can lie in the
        // arguments and not at the head.
        let unresolved = |arity| LoweringRefusal::UnresolvedTypeHead {
            span: site.at.span,
            head: head.span,
            name,
            arity,
        };
        let (Some(argument), 1_usize) = (first, count)
        else {
            return Err(unresolved(HeadArity::Polyadic(OperandCount::from(count))));
        };
        let Maybe::Present(former) = former
        else {
            return Err(unresolved(HeadArity::Unary));
        };

        self.apply_former(site, former, argument)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The nullary type atom `name` spells in the source being lowered: an
    /// ambient atom, or one a listed import of its home binds,
    /// `import std.buffer (Buf);` (#4522).
    ///
    /// # Specification
    /// - requires: nothing — every identifier is admissible input.
    /// - ensures: the ambient table's answer when it has one; else the atom
    ///   that the home of a resolved listed import of the current source
    ///   answers under `name`; else the absence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a buffer type in a source that lists `Buf` from
    ///   `std.buffer` lowers to the native buffer, and one in a source that
    ///   does not is an unresolved head.
    /// - witness: `gandr-surface-lowering::lower::tests::a_buffer_type_resolves_only_through_its_listing_4522`
    #[spec(
        ensures: |ret| match type_atom(name) {
            | Maybe::Present(ambient) => ret == Maybe::Present(ambient),
            | Maybe::Absent(_) => true,
        },
    )]
    #[inline]
    pub fn atom(
        &self,
        name: SurfaceName<'source>,
    ) -> Maybe<TypeAtom, type_head::Absent>
    {
        let ambient = type_atom(name);
        if let Maybe::Present(_) = ambient {
            return ambient;
        }
        self.cx()
            .listed_head(name, homed_atom)
            .map_or(ambient, Maybe::Present)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// The type former `member` spells after `qualifier` at `site`, `l.List`
    /// or `std.list.List`, when `qualifier` is the alias or the module path of
    /// a resolved import of the site's source whose module homes it.
    ///
    /// # Specification
    /// - requires: `qualifier` is the qualifier of the type path at `site` and
    ///   `member` its selected name.
    /// - ensures: the former [`homed_former`] answers at the module path the
    ///   import `qualifier` binds names, under `member`'s name, when that
    ///   import resolved to a source, the import then reached; none when
    ///   `qualifier` binds no import, its import names an address or did not
    ///   resolve, or its module homes no such former.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the import's lookup.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list type read through a whole import's module path
    ///   and through an alias lowers to the native list, a head the module does
    ///   not home is an unknown member, and a module path no import binds is an
    ///   unresolved head.
    /// - witness: `gandr-surface-lowering::lower::tests::a_homed_former_reads_through_its_import_s_qualifier_4862`
    fn qualified_former(
        &mut self,
        site: Site,
        qualifier: Placed,
        member: Placed,
    ) -> Option<TypeFormer>
    {
        let source = self.cx().collected.unit.source_at(site.at.span.start());
        let module = self
            .cx()
            .tree
            .spanned(qualifier.span)
            .map_or_else(|| self.cx().name_at(qualifier), SurfaceName::from);
        let Maybe::Present(import) = self.cx().collected.imports.aliased(source, module)
        else {
            return None;
        };
        let (ImportResolution::Path(ImportTarget::Source(_)), Maybe::Present(home)) =
            (import.resolution(), import.module())
        else {
            return None;
        };
        let Maybe::Present(former) = homed_former(home, self.cx().name_at(member))
        else {
            return None;
        };
        let span = import.span();
        self.cx_mut().collected.reach(span);
        Some(former)
    }

    /// The type former `head`, the head of a call written at `site`, spells.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: the head's name when it is a capitalised name spelling
    ///   `Path`, `Flow`, `Stack`, `Iso`, `Model`, `Terms` or a unary type
    ///   former, and no constructor, binder, earlier declaration or stated type
    ///   carries that name; the unformed absence for any other head.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold; the refusals the name's resolution yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path type and a list type written as calls where a
    ///   value is read are read as their formers, while a constructor and a
    ///   data family applied the same way keep their own readings.
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_applies_to_its_fields`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body reads the head's spelling once; the check reads it once more"
        )
    )]
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(name)) => name == self.cx().name_at(head),
            | _ => true,
        },
    )]
    fn former_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<SurfaceName<'source>, formed::Absent>, LoweringRefusal<'source>>
    {
        let unformed = Maybe::Absent(formed::Absent::Unformed);
        let Some(node) = self.cx().tree.node(head.node)
        else {
            return Ok(unformed);
        };
        let Shape::Form {
            former: Former::Constructor,
            ..
        } = shape_of(self.cx().pbg, node)?
        else {
            return Ok(unformed);
        };
        let name = self.cx().name_at(head);
        let spelled = [
            TileName::PATH.as_ref(),
            TileName::BRIDGE.as_ref(),
            identity::FLOW,
            STACK,
            identity::ISO,
            MODEL,
            TERMS,
        ]
        .contains(&name.as_ref())
            || matches!(self.cx().former(name), Maybe::Present(_));
        if !spelled {
            return Ok(unformed);
        }
        if let Maybe::Present(_constructor) = Native::new(self.host()).constructor_named(site, name)
        {
            return Ok(unformed);
        }
        let named = Site { at: head, ..site };
        if let Maybe::Present(_shadowed) = self.resolve_name(named, site.reading.frame(), name)? {
            return Ok(unformed);
        }
        if let Maybe::Present(_stated) = self.stated_named(site, name)? {
            return Ok(unformed);
        }

        Ok(Maybe::Present(name))
    }

    /// Classify a continuation's type, `Stack(C, D)`, its two operands already
    /// read off the application.
    ///
    /// # Specification
    /// - requires: `site` is a type application headed `Stack`, which nothing
    ///   the scope binds answers, written over `input` and `output`.
    /// - ensures: the form stands as a value type, reads both operands as
    ///   computation types under its own frame, and is planned over the two in
    ///   order.
    /// - provides: the written spelling of the type a captured continuation
    ///   has, the spelling its presentation writes.
    /// - fails: yields the wrong-sort refusal where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a continuation type written over two returners, read
    ///   back out of the arena with its input and output in order.
    /// - witness: `gandr-surface-lowering::lower::tests::a_written_stack_type_lowers_to_its_continuation_type_401`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&Plan::Stack(input, output))
                        if [input, output] == written
                            && self.cx().reading(input) == Reading::CompType(site.reading.frame())
                            && self.cx().reading(output) == Reading::CompType(site.reading.frame())
                )
        },
    )]
    fn stack_type(
        &mut self,
        site: Site,
        written: [NodeIndex; 2],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let [input, output] = written;
        self.read(input, Reading::CompType(frame));
        self.read(output, Reading::CompType(frame));
        self.plan(site, Plan::Stack(input, output));

        Ok(())
    }

    /// What the form at `at`, not yet classified, states to a call a binder
    /// declared at it heads: the reading [`Self::type_application`] gives it,
    /// taken without classifying it.
    ///
    /// # Specification
    /// - requires: `at` holds the reading it is classified under.
    /// - ensures: [`capability::Stated::Stack`] exactly when the form at `at`
    ///   is a type application headed `Stack` over two operands, which fixes no
    ///   sorts, whose head is no constructor where a value is read, no type
    ///   family the scope states and no name the scope resolves, so that
    ///   classifying it plans it as [`Plan::Stack`]; a refusal on the way
    ///   answers [`capability::Stated::Other`] and is left to the form's own
    ///   classification; no plan, resolution or operand is kept.
    /// - fails: an engine fault: the lowering's allowance spent, or a mold the
    ///   grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The engine fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member abbreviating a stack, read from a
    ///   declaration classified before the member is, states the stack.
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_stated_stack_is_resumed_as_a_clause_resumes_1387`
    #[spec(
        captures: before = (self.cx().plans.count(), self.cx().resolutions.len(), self.cx().operands.entries().len()),
        ensures: |_| self.cx().plans.count() == before.0
            && self.cx().resolutions.len() == before.1
            && self.cx().operands.entries().len() == before.2,
    )]
    #[inline]
    pub fn written_stack(
        &mut self,
        at: NodeIndex,
    ) -> Result<capability::Stated, LoweringRefusal<'source>>
    {
        let other = Ok(capability::Stated::Other);
        let Some(node) = self.cx().tree.node(at)
        else {
            return other;
        };
        let Shape::Form {
            name,
            former: Former::TypeApplication,
        } = shape_of(self.cx().pbg, node)?
        else {
            return other;
        };
        let site = Site {
            at: Placed::of(at, node),
            name,
            reading: self.cx().reading(at),
        };
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let start = self.cx().operands.entries().len();
        let read = read_pieces(self.cx().pbg, self.cx().tree, at, &mut scratch);
        let mut cursor = Cursor::new(&scratch.pieces, site.at.span);
        let head = match cursor.type_head() {
            Maybe::Present(head) => Some(head),
            Maybe::Absent(_) => None,
        };
        let shaped = read.is_ok()
            && head.is_some_and(|head| self.cx().name_at(head).as_ref() == STACK)
            && arguments(site, &mut cursor, &mut self.cx_mut().operands).is_ok()
            && self.cx().operands.entries().len().saturating_sub(start) == 2_usize;
        self.cx_mut().operands.truncate(At::from(start));
        self.cx_mut().scratch = scratch;
        let Some(head) = head.filter(|_| shaped)
        else {
            return other;
        };
        if self
            .cx()
            .fixed_sorts
            .get(&at)
            .is_some_and(|sorts| !sorts.is_empty())
        {
            return other;
        }
        let name = self.cx().name_at(head);
        if let Reading::Value(_) = site.reading
            && let Maybe::Present(_) = Native::new(self.host()).constructor_named(site, name)
        {
            return other;
        }
        let unresolved = match self.stated_named(site, name) {
            Ok(Maybe::Present(TypeComponent {
                meaning: TypeMeaning::Family(_),
                ..
            })) => Ok(capability::Stated::Other),
            Ok(Maybe::Present(_) | Maybe::Absent(_)) => {
                let named = Site { at: head, ..site };
                self.resolve_name(named, site.reading.frame(), name).map(
                    |resolved| match resolved {
                        Maybe::Absent(named::Absent::Unresolved) => capability::Stated::Stack,
                        Maybe::Present(_) => capability::Stated::Other,
                    },
                )
            },
            Err(refusal) => Err(refusal),
        };

        match unresolved {
            Err(refusal) if refusal.classify() == FailureClass::EngineFault => Err(refusal),
            Err(_) => other,
            Ok(stated) => Ok(stated),
        }
    }

    /// Classify the static application of the code `resolved` names to the
    /// arguments `applied` holds in the operand store, the head written as
    /// `lists` states.
    ///
    /// # Specification
    /// - requires: `applied` is a stretch of the operand store, each entry an
    ///   argument the application was written with, left to right; a second
    ///   list `lists` names is the stretch after it.
    /// - ensures: a head written with a list is called, even by an empty one,
    ///   `f()`; a dynamic function's result applied by a second list where a
    ///   type is read, `f(a)(b)`, is the decode of the code that application
    ///   returns, in the universe the code's written type reaches after one
    ///   arrow per argument of both lists (#5213). With no second list, a data
    ///   family stands as the nominal type over its arguments, each read as a
    ///   value under the site's frame, which a value position quotes.
    ///   Otherwise, where a value is read, the application stands as itself;
    ///   where a type is read, it stands as the decode of the application, in
    ///   the universe the code's written type reaches after one arrow per
    ///   argument, and else in the universe the position reads — the
    ///   computation types where only a computation type is read, the value
    ///   types everywhere else, at the fuss-free level. A dynamic function — a
    ///   declaration defined by a function tail, or a binder applied to at
    ///   least one argument whose written type is a thunk or which is written
    ///   with no type — is not a static operator: where a type is read, its
    ///   application is the unquote of the code the call returns, in the
    ///   universe the position reads, and where a value is read, an application
    ///   of it to at least one argument is the call, a computation the position
    ///   nests. A call of it with no argument, `f()`, is the force of its head
    ///   where a value is read, as the expression grammar reads `f()` (#6787).
    ///   In a static abstraction's body, the type its operator denotes, that
    ///   call is the unquote a type reads, and the body quotes it; its
    ///   telescope is read once that quote is chosen (#3786). Every argument is
    ///   read as a value under the site's frame, and a binder so named is
    ///   recorded by
    ///   [`Self::name_in_type`](crate::lower::Expressions::name_in_type):
    ///   quoted in a body quote, mentioned elsewhere. Each argument of a decode
    ///   or an unquote counts in the type's telescope, as a family's arguments
    ///   do, so a lambda among them reads each variable from outside it at its
    ///   index.
    /// - provides: the one reading of a type operator's use, bare or applied,
    ///   as a value or as the type it denotes.
    /// - fails: yields the arity refusal for a data family applied to other
    ///   than its parameter count, and for a dynamic function named bare where
    ///   a type is read, which computes a code only once applied (#690); the
    ///   wrong-sort refusal where the position reads neither a value nor the
    ///   sort of the decode's universe, and for a flattened model implicit,
    ///   which is its components and no value (`ModelsRef::unflattened`);
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the walk of the
    ///   code's type.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Termination
    /// The argument loop runs once per entry of the finite stretch `applied`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare head and an applied one, each where a value is
    ///   read and where a type is read, the decode's universe written by the
    ///   operator and left to the position, a function called where a type is
    ///   read, and a binder holding a thunk called where a type is read and in
    ///   a type-position call's argument, each asserted as the exact core node
    ///   read back out of the arena; a lambda in a type-valued call's argument,
    ///   in a signature's type, reading outer variables at their indices; a
    ///   binder holding a family called in a body's static abstraction, past a
    ///   parameter no type names; a function called with no argument at a
    ///   family's argument, in the call form and in the juxtaposed form.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_family_applies_to_its_parameters`
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_to_a_universe_unquotes_where_a_type_is_read`
    /// - witness: `gandr-surface-lowering::lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_a_type_valued_call_reads_outer_variables_at_their_indices_3616`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_transport_moves_through_a_family_a_parameter_names_3786`
    /// - witness: `gandr-surface-lowering::lower::tests::a_nullary_call_at_a_family_s_argument_is_its_head_s_force_6787`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.cx().plans.get(site.at.node) {
                    | Some(&Plan::StaticApplication(_, planned)) => {
                        planned == self.cx().kept(applied) && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Called(_, planned)) => {
                        planned == self.cx().kept(applied)
                            && applied.start < applied.end
                            && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Forced(_)) => {
                        applied.start == applied.end && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Decode(_, planned, _) | &Plan::Unquote(_, planned, _)) => {
                        planned == self.cx().kept(applied)
                            && (!matches!(site.reading, Reading::Value(_))
                                || self.cx().static_bodies.contains(&site.at.node))
                    },
                    | Some(&Plan::Reapplied(_, planned, again, _)) => {
                        planned == self.cx().kept(applied)
                            && matches!(lists, Lists::Again(written) if self.cx().kept(written) == again)
                    },
                    | Some(&(Plan::Data(_, planned) | Plan::Codata(_, planned))) => planned == self.cx().kept(applied),
                    | _ => false,
                }
        },
    )]
    fn listed_application(
        &mut self,
        site: Site,
        resolved: Resolved,
        applied: Stretch,
        lists: Lists,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        ModelsRef::new(self.host_ref()).unflattened(site, resolved)?;
        let again = match lists {
            Lists::Again(again) => Some(again),
            Lists::Bare | Lists::Called => None,
        };
        if again.is_none()
            && let Resolved::Declaration { constant, .. } = resolved
            && let Maybe::Present(arity) = NativeRef::over(self.cx()).data_family(constant)
        {
            return Native::new(self.host()).family(site, constant, arity, applied);
        }
        if again.is_none()
            && let Resolved::Declaration { constant, .. } = resolved
            && let Maybe::Present(arity) = NativeRef::over(self.cx()).codata_family(constant)
        {
            return Native::new(self.host()).codata_type(site, constant, arity, applied);
        }
        let from = site.reading.frame();
        let declared = match resolved {
            Resolved::Binder(bound) => bound.declared,
            Resolved::Declaration { declared, .. } => declared,
        };
        // A list written after the head calls it, even an empty one, `f()`
        // (#5213).
        let called = applied.start < applied.end || lists != Lists::Bare;
        let dynamic = match resolved {
            Resolved::Declaration { constant, .. } => matches!(
                self.cx()
                    .collected
                    .slots
                    .get(usize::from(constant))
                    .map(|slot| slot.definition),
                Some(Maybe::Present(Half {
                    operand: Operand::Function,
                    ..
                }))
            ),
            // A binder holds a function when its written type is a thunk, the
            // bridge or the alias, or a type family that stands for one, or
            // when it is written with no type: a pattern's field or a `let`'s
            // result. A static lambda's operand is an operator, and its
            // application is static.
            Resolved::Binder(_) => {
                called
                    && match declared {
                        Maybe::Present(written) => self.holds_function(written)?.0,
                        Maybe::Absent(binder_type::Absent::Untyped) => true,
                        Maybe::Absent(
                            binder_type::Absent::Operand | binder_type::Absent::Instance,
                        ) => false,
                    }
            },
        };
        // A static abstraction's body is the type its operator denotes, so a
        // dynamic call written there is the type of the code it returns, and
        // the body quotes it (#3786).
        let decoded = !matches!(site.reading, Reading::Value(_))
            || (dynamic && called && self.cx().static_bodies.contains(&site.at.node));
        // A second list applies a function's result where a type is read, and
        // nothing else (#5213).
        if let Some(again) = again
            && (!dynamic || !decoded)
        {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(
                again.end.saturating_sub(again.start),
            ))));
        }
        let universe = if decoded {
            let written = applied.end.saturating_sub(applied.start).saturating_add(
                again.map_or(0_usize, |again| again.end.saturating_sub(again.start)),
            );
            let count = OperandCount::from(written);
            if dynamic && !called {
                return Err(site.out(FragmentBoundary::Arity(count)));
            }
            Some(self.written_universe(declared, count, site.reading.positional_universe())?)
        }
        else {
            None
        };
        let produced = match universe {
            Some(Universe {
                sort: GroundSort::Value,
                ..
            }) => Produced::ValueType,
            Some(Universe {
                sort: GroundSort::Computation,
                ..
            }) => Produced::CompType,
            None if dynamic && called => Produced::Computation,
            None => Produced::Value,
        };
        let frame = self.require(site, produced)?;
        // The telescope is read once the bridge is chosen: a quote the bridge
        // inserts counts the code in its own.
        let code = match resolved {
            Resolved::Binder(bound) => Code::Bound {
                from,
                binder: bound.binder,
                telescope: self.shared().telescope_at(site.at.node),
            },
            Resolved::Declaration { constant, .. } => Code::Constant(constant),
        };
        let kept = self.cx().kept(applied);
        let plan = match (universe, again) {
            (Some(universe), Some(again)) => {
                Plan::Reapplied(code, kept, self.cx().kept(again), universe)
            },
            (Some(universe), None) if dynamic => Plan::Unquote(code, kept, universe),
            (Some(universe), None) => Plan::Decode(code, kept, universe),
            // A call with no argument is the force of its head, as the
            // expression grammar reads `f()` (#6787).
            (None, _) if dynamic && called && applied.start == applied.end => Plan::Forced(code),
            (None, _) if dynamic && called => Plan::Called(code, kept),
            (None, _) => Plan::StaticApplication(code, kept),
        };
        if let Code::Bound { binder, .. } = code {
            let _telescope = self.name_in_type(site.at.node, binder);
        }
        // An argument at a parameter the operator's classifier states as a
        // static arrow is a type operator where it is a lambda (#4508).
        if !dynamic && let Maybe::Present(written) = declared {
            let mut classifier = written;
            for position in applied.start .. applied.end {
                let Some((domain, codomain)) = self.static_arrow(classifier)?
                else {
                    break;
                };
                if let Some(&argument) = self.cx().operands.entries().get(position)
                    && self.static_arrow(domain)?.is_some()
                {
                    let _first = self
                        .cx_mut()
                        .static_lambdas
                        .insert(argument, Maybe::Present(domain));
                }
                classifier = codomain;
            }
        }
        let read = Stretch {
            start: applied.start,
            end: again.map_or(applied.end, |again| again.end),
        };
        self.valued_arguments(resolved, read)?;
        self.plan_applied(site, plan, read, frame);

        Ok(())
    }

    /// As [`Self::listed_application`], the head written with no list or with
    /// the one list `applied` holds.
    ///
    /// # Specification
    /// trivial.
    fn static_application(
        &mut self,
        site: Site,
        resolved: Resolved,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.listed_application(site, resolved, applied, Lists::Bare)
    }

    /// Read the head `resolved` as the call a type path or a type's call form
    /// writes: applied to the arguments `applied` holds, and its result to
    /// those `again` holds when it writes a second list (#5213). A head written
    /// with no list stands bare.
    ///
    /// # Specification
    /// trivial.
    fn call_resolved(
        &mut self,
        site: Site,
        resolved: Resolved,
        applied: Option<Stretch>,
        again: Option<Stretch>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let none = Stretch {
            start: self.cx().operands.entries().len(),
            end: self.cx().operands.entries().len(),
        };
        match (applied, again) {
            (Some(first), Some(second)) => {
                self.listed_application(site, resolved, first, Lists::Again(second))
            },
            (Some(first), None) => self.listed_application(site, resolved, first, Lists::Called),
            (None, _) => self.static_application(site, resolved, none),
        }
    }

    /// Whether a binder whose type is written at `written` holds a function:
    /// the type is a thunk or the box `A -> B`, read
    /// through each type family it names to the type the family stands for.
    ///
    /// # Specification
    /// - requires: `written` is a node of the tree, its plan made.
    /// - ensures: `true` exactly when the walk meets a thunk type or a box, as
    ///   [`crate::form::writes_box`] reads it, before any other form.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    /// - executable: none — the answer is a walk of the plans and the tree,
    ///   which a predicate could check only by repeating the walk.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at the bridge, at a type member
    ///   standing for the bridge and at a model's type member standing for it,
    ///   each called where a type is read and observed through the unquote it
    ///   plans.
    /// - witness: `gandr-surface-lowering::lower::tests::a_binder_at_a_family_standing_for_a_function_unquotes_its_call_522`
    /// - witness: `gandr-surface-lowering::lower::tests::a_box_passes_a_lambda_applies_states_a_motive_and_matches_its_columns_4853`
    fn holds_function(
        &mut self,
        written: NodeIndex,
    ) -> Result<HoldsFunction, LoweringRefusal<'source>>
    {
        let mut position = written;
        loop {
            self.cx_mut().fuel.spend()?;
            if let Some(&Plan::Expansion(family, _)) = self.cx().plans.get(position) {
                let Some(member) = self.cx().collected.families.get(family.0)
                else {
                    return Ok(HoldsFunction(false));
                };
                position = member.defined.node;
                continue;
            }
            let Some(node) = self.cx().tree.node(position)
            else {
                return Ok(HoldsFunction(false));
            };
            let thunked = matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::ThunkType,
                    ..
                })
            );
            return Ok(HoldsFunction(thunked || self.boxes(position)?.0));
        }
    }

    /// Classify a type former written as its own keyword: `+U C` or `-F A`,
    /// or the row a definition's result writes before its type, `[E] A`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk type or a returner type in type position.
    /// - ensures: the keyword resolves against the unary table, a thunk type's
    ///   grade `[ω]` reads as no grade written, a returner's bracket reads as
    ///   its effect row, a row before a result's type reads as the inserted
    ///   returner's, `-F [E] A`, the form stands at the sort its former
    ///   produces, reads its one operand at the sort the former takes, and is
    ///   planned over it. A returner of a group of outputs, `-F (A, B)`, stands
    ///   as the group.
    /// - provides: the keyword spelling of the two type formers.
    /// - fails: yields the unresolved-head refusal for a keyword no former
    ///   answers, [`LoweringRefusal::GradedBridge`] for a thunk type graded
    ///   other than `ω`, the row's refusal for a returner's, the not-at-result
    ///   refusal for a row before a type anywhere but a definition's result,
    ///   the unadmitted refusal for a bracket on a list type, the wrong-sort
    ///   refusal for a former whose sort does not suit the position, and the
    ///   hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the thunk and returner spellings plan their
    ///   respective bridge former, while unsupported grades produce a located
    ///   refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::a_graded_bridge_is_refused_by_name`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_returner_row_names_whole_interfaces`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Former(_, _) | Plan::Effectful(..) | Plan::Transparent(_)))
                )
        },
    )]
    fn formed_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        // `[E] B` at a definition's result: the row of the returner the
        // lowering inserts there, `-F [E] B`; nowhere else is it a result.
        if label == TileName::BRACKET_OPEN {
            let Reading::Result(_) = site.reading
            else {
                return Err(site.out(FragmentBoundary::NotAtResult));
            };
            let _open = cursor.tile(TileName::BRACKET_OPEN);
            let row = CapabilityRef::new(self.host_ref()).returner_row(site, &mut cursor)?;
            let argument = site.one(cursor.operands())?;
            exhausted(site, &cursor)?;
            return Capability::new(self.host()).effectful(site, row, argument);
        }
        let _keyword = cursor.tile(label);
        let name = self.cx().name_at(at);
        let Maybe::Present(former) = self.cx().former(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: at.span,
                head: at.span,
                name,
                arity: HeadArity::Unary,
            });
        };
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            match former {
                TypeFormer::Thunk => self.shared().grade(site, &mut cursor)?,
                TypeFormer::Returner => {
                    let row =
                        CapabilityRef::new(self.host_ref()).returner_row(site, &mut cursor)?;
                    let argument = site.one(cursor.operands())?;
                    exhausted(site, &cursor)?;
                    return Capability::new(self.host()).effectful(site, row, argument);
                },
                TypeFormer::List | TypeFormer::Run | TypeFormer::Prefix | TypeFormer::Dialogue => {
                    return Err(site.folded(
                        FormName::GRADE,
                        FragmentBoundary::Unadmitted(Unbuilt::TypeGrade),
                    ));
                },
            }
        }
        let argument = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;

        self.apply_former(site, former, argument.node)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Read a bridge's grade, `[r]`, admitting only the default `ω`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `ω` followed by `]` reads as the bridge with no grade
    ///   written, the cursor past the `]`.
    /// - provides: the one grade the core's bridge carries.
    /// - fails: [`LoweringRefusal::GradedBridge`] for a numeral or a name as
    ///   the grade, at the grade; a misplaced-tile fault for a grade out of
    ///   shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the default grade, a numeral and a name, each
    ///   asserted as the lowered bridge or the exact refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::a_graded_bridge_is_refused_by_name`
    #[spec(
        captures: input = {
            let mut input = cursor.clone();
            (input.read(), input.read(), input.peek())
        },
        ensures: |ret| {
            ret.is_ok()
                == matches!(
                    input,
                    (
                        Maybe::Present(Piece::Tile {
                            label: TileName::OMEGA,
                            ..
                        }),
                        Maybe::Present(Piece::Tile {
                            label: TileName::BRACKET_CLOSE,
                            ..
                        }),
                        _
                    )
                )
                && (ret.is_err() || cursor.peek() == input.2)
        },
    )]
    fn grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if label == TileName::NUMBER || label == TileName::IDENTIFIER {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.cx().name_at(at),
            });
        }
        closed(site, cursor, TileName::OMEGA)?;

        closed(site, cursor, TileName::BRACKET_CLOSE)
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Plan `former` applied to `argument` at `site`.
    ///
    /// # Specification
    /// - requires: `argument` is the one operand the former was written with.
    /// - ensures: the thunk former stands at value-type sort with its argument
    ///   read at computation-type sort, the returner former stands at
    ///   computation-type sort with its argument read at value-type sort, or,
    ///   for a group of outputs `-F (A, B)`, adopts the group read as a result,
    ///   the list former stands at value-type sort with its element type read
    ///   at value-type sort, and the run former stands at value-type sort with
    ///   its session code read as a value; the former decides both, so nothing
    ///   is pushed down that has to be re-derived.
    /// - provides: the one place a type former's sorts are decided.
    /// - fails: yields the wrong-sort refusal for a former whose produced sort
    ///   does not suit the position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — thunk and returner read the argument in opposite
    ///   sorts; each then lowers to its own core bridge former, not the other
    ///   one; a list reads its element type as a value type; the returner of a
    ///   group is the group a result writes.
    /// - witness: `gandr-surface-lowering::lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_group_of_outputs_is_the_many_value_returner`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (matches!(self.cx().plans.get(site.at.node), Some(&Plan::Former(stored, child)) if stored == former && child == argument)
                    && self.cx().reading(argument)
                        == match former {
                            | TypeFormer::Thunk => Reading::CompType(site.reading.frame()),
                            | TypeFormer::Returner | TypeFormer::List => Reading::ValueType(site.reading.frame()),
                            | TypeFormer::Run | TypeFormer::Prefix | TypeFormer::Dialogue => Reading::Value(site.reading.frame()),
                        })
                || (former == TypeFormer::Returner
                    && matches!(self.cx().plans.get(site.at.node), Some(&Plan::Transparent(child)) if child == argument)
                    && self.cx().reading(argument) == Reading::Result(site.reading.frame()))
        },
    )]
    fn apply_former(
        &mut self,
        site: Site,
        former: TypeFormer,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match former {
            TypeFormer::Thunk
            | TypeFormer::List
            | TypeFormer::Run
            | TypeFormer::Prefix
            | TypeFormer::Dialogue => Produced::ValueType,
            TypeFormer::Returner => Produced::CompType,
        };
        let frame = self.require(site, produced)?;
        // The returner of a group of outputs is the group a result writes,
        // `-F (A, B)` as `-> (A, B)`.
        if former == TypeFormer::Returner
            && let Some(tree) = self.cx().tree.node(argument)
            && Models::new(self.host())
                .written_group(Placed::of(argument, tree), frame)?
                .0
        {
            self.read(argument, Reading::Result(frame));
            self.plan(site, Plan::Transparent(argument));
            return Ok(());
        }
        let inner = match former {
            TypeFormer::Thunk => Reading::CompType(frame),
            TypeFormer::Returner | TypeFormer::List => Reading::ValueType(frame),
            TypeFormer::Run | TypeFormer::Prefix | TypeFormer::Dialogue => Reading::Value(frame),
        };
        self.read(argument, inner);

        self.plan(site, Plan::Former(former, argument));

        Ok(())
    }

    /// Classify an arrow type: the computation arrow `A -> C`, the dependent
    /// arrow `(x : A) -> C`, and where a value type is read the static Pi
    /// `A -> B` of a type operator or the box `A -> B` of a function value.
    ///
    /// # Specification
    /// - requires: `site` is an arrow in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: an arrow standing as a value type, or at a definition's
    ///   result, where the returner is inserted over it, that is written as a
    ///   kind, or whose domain and codomain both classify codes, as
    ///   [`Self::ranges_over_codes`] reads them, is the static Pi, its domain
    ///   and codomain each read as a value type under the arrow's own frame,
    ///   since the codomain binds nothing, and a kind's codomain is a kind; any
    ///   other arrow standing so is the box [`Self::boxed`] plans, the value
    ///   function `=>` writes, so no arrow at a result is curried. An arrow
    ///   quoted in a term stands so too, unless [`Self::writes_computation`]
    ///   reads it as written as a computation type: a type operator's argument
    ///   or a type family's body writes the box as `=>` did. Any other arrow
    ///   stands as a computation type: one whose domain is one binder is the
    ///   dependent arrow `Models::dependent_arrow` plans, and the rest read
    ///   their domain as a value type and their codomain as a computation type.
    ///   Each is planned over both operands.
    /// - provides: the function type of the fragment, the box of a function
    ///   value and the classifier of a type operator.
    /// - fails: yields the wrong-sort refusal where neither sort suits the
    ///   position, the chained-arrow refusal for a box whose output is an arrow
    ///   written without parentheses, and either hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The arrow's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arrow where a computation type is read, where a
    ///   value type is read over universes, nested to the right as an
    ///   operator's classifier, over a computation codomain where a value type
    ///   is read, a box over value types, a box from a universe to a value
    ///   type, a kind over a type that classifies no codes, and an arrow quoted
    ///   in a term over a value type and over a returner, each asserted as the
    ///   exact core node read back out of the arena or the exact refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::an_arrow_from_a_universe_to_a_value_type_is_the_box_5203`
    /// - witness: `gandr-surface-lowering::lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    /// - witness: `gandr-surface-lowering::lower::tests::a_computation_codomain_of_a_box_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `gandr-surface-lowering::lower::tests::a_quoted_arrow_is_the_box_its_thunk_spells_4853`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_body_after_equals_is_its_block_4853`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_dependent_arrow_is_the_telescope_the_alias_abbreviates`
    /// - witness: `gandr-surface-lowering::tests::modules::a_kinded_type_component_forms_at_its_classifier`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.cx().plans.get(site.at.node) {
                    | Some(&(Plan::StaticPi(..) | Plan::ValueFunction(..) | Plan::Telescope(..))) => matches!(site.reading, Reading::ValueType(_) | Reading::Result(_) | Reading::Value(_)),
                    | Some(&(Plan::Arrow(..) | Plan::DependentArrow(..))) => !matches!(site.reading, Reading::ValueType(_) | Reading::Result(_)),
                    | _ => false,
                }
        },
    )]
    fn arrow(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // A type quoted in a term is the box, unless it is written as a
        // computation type.
        let quoted_box =
            matches!(site.reading, Reading::Value(_)) && !self.writes_computation(site.at)?.0;
        let value_typed =
            matches!(site.reading, Reading::ValueType(_) | Reading::Result(_)) || quoted_box;
        let produced = if value_typed {
            Produced::ValueType
        }
        else {
            Produced::CompType
        };
        let frame = self.require(site, produced)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let kind = self.cx().kinds.contains(&site.at.node);
        // The static Pi is a type operator: both its domain and its codomain
        // classify codes. Any other arrow where a value type is read is the
        // box.
        let kinded = self.ranges_over_codes(domain)?.0 && self.ranges_over_codes(codomain)?.0;
        let boxes = value_typed && !kinded;
        // In a kind, the box is a family's telescope, `(a : A, …) -> U`; a
        // bare domain stays the static Pi, whose classifier the checker reads.
        if boxes
            && kind
            && Models::new(self.host()).telescope_function(site, frame, domain, codomain)?
                == arity::Planned(true)
        {
            return Ok(());
        }
        if boxes && !kind {
            // A box whose output is a box writes the output in parentheses,
            // `A -> (B -> C)`; a flat box writes its inputs as one group,
            // `(A, B) -> C`.
            if matches!(self.cx().form_at(codomain)?, Some((_, Former::ArrowType))) {
                return Err(site.out(FragmentBoundary::ChainedArrow));
            }
            return self.boxed(site, frame, domain, codomain);
        }
        if !value_typed
            && Models::new(self.host()).dependent_arrow(site, frame, domain, codomain)?
                == arity::Planned(true)
        {
            return Ok(());
        }
        self.read(domain.node, Reading::ValueType(frame));
        if value_typed {
            if kind {
                let _fresh = self.cx_mut().kinds.insert(codomain.node);
            }
            self.read(codomain.node, Reading::ValueType(frame));
            self.plan(site, Plan::StaticPi(domain.node, codomain.node));
        }
        else {
            self.read(codomain.node, Reading::CompType(frame));
            self.plan(site, Plan::Arrow(domain.node, codomain.node));
        }

        Ok(())
    }

    /// Whether the type written at `domain` classifies codes, as
    /// [`crate::form::classifies_codes`] reads it over this lowering's
    /// scratch buffer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`crate::form::classifies_codes`].
    /// - fails: as [`crate::form::classifies_codes`].
    /// - panics: none.
    /// - executable: none — the answer is read off the syntax tree, which a
    ///   predicate could check only by repeating the walk.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::form::classifies_codes`].
    /// - witness: `gandr-surface-lowering::lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    fn ranges_over_codes(
        &mut self,
        domain: Placed,
    ) -> Result<crate::form::Kinded, LoweringRefusal<'source>>
    {
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let read = crate::form::classifies_codes(
            self.cx().pbg,
            self.cx().tree,
            domain,
            &mut scratch,
            &mut self.cx_mut().classified,
        );
        self.cx_mut().scratch = scratch;
        read
    }

    /// Whether the type written at `at` is the box, as
    /// [`crate::form::writes_box`] reads it over this lowering's scratch
    /// buffer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`crate::form::writes_box`].
    /// - fails: as [`crate::form::writes_box`].
    /// - panics: none.
    /// - executable: none — the answer is read off the syntax tree, which a
    ///   predicate could check only by repeating the walk.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::form::writes_box`].
    /// - witness: `gandr-surface-lowering::lower::tests::a_box_passes_a_lambda_applies_states_a_motive_and_matches_its_columns_4853`
    #[inline]
    pub fn boxes(
        &mut self,
        at: NodeIndex,
    ) -> Result<crate::form::Boxed, LoweringRefusal<'source>>
    {
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let read = crate::form::writes_box(self.cx().pbg, self.cx().tree, at, &mut scratch);
        self.cx_mut().scratch = scratch;
        read
    }

    /// Whether the type written at `at` is written as a computation type, by
    /// its syntax: a returner, a lazy product or a lazy record, or an arrow
    /// whose output is written so, through the parentheses of one entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: computed for `-F B`, `-F [E] B`, `C & D`, `&{ .l : C }`, `A
    ///   -> -F B` and `A -> B -> -F C`, and through one pair of parentheses
    ///   around each; not computed for any other type: `A -> B`, `A -> (B ->
    ///   C)` and a group of several entries.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    /// - executable: none — the answer is read off the syntax tree, which a
    ///   predicate could check only by repeating the walk.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Termination
    /// Each round descends to an operand of the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arrow`]: a quoted arrow over a value type
    ///   is the box and one over a returner the computation arrow.
    /// - witness: `gandr-surface-lowering::lower::tests::a_quoted_arrow_is_the_box_its_thunk_spells_4853`
    fn writes_computation(
        &mut self,
        at: Placed,
    ) -> Result<arity::Computed, LoweringRefusal<'source>>
    {
        let mut at = at;
        loop {
            let arrow = match self.cx().form_at(at)? {
                Some((
                    _,
                    Former::ReturnerType | Former::LazyProductType | Former::LazyRecordType,
                )) => {
                    return Ok(arity::Computed(true));
                },
                Some((_, Former::ArrowType)) => true,
                Some((_, Former::ParenthesizedType)) => false,
                _ => return Ok(arity::Computed(false)),
            };
            let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
            let read =
                read_pieces(self.cx().pbg, self.cx().tree, at.node, &mut scratch).map(|()| {
                    let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                        Piece::Operand(operand) => Some(operand),
                        Piece::Tile { .. } => None,
                    });
                    // An arrow's output is its last operand; parentheses group
                    // only around one entry.
                    if arrow {
                        operands.next_back()
                    }
                    else {
                        match (operands.next(), operands.next()) {
                            (Some(sole), None) => Some(sole),
                            (Some(_), Some(_)) | (None, _) => None,
                        }
                    }
                });
            self.cx_mut().scratch = scratch;
            let Some(next) = read?
            else {
                return Ok(arity::Computed(false));
            };
            at = next;
        }
    }

    /// Classify an eager product type, `A * B`, a sum type, `A + B`, or a lazy
    /// product type, `C & D`, and the chain it heads; `former` names which.
    ///
    /// # Specification
    /// - requires: `site` is a product, a sum or a lazy product in type
    ///   position, or a product or a sum in value position where a type is
    ///   quoted, and `former` is its former.
    /// - ensures: the chain stands as a value type, or as a computation type
    ///   for the lazy product; an operand that is itself an unparenthesized
    ///   form of `former` contributes its own operands instead, so a chain `A *
    ///   B * C` is one product of three components, `A + B + C` one sum of
    ///   three summands and `C & D & E` one lazy product of three components
    ///   however each associates, while `(A * B) * C` keeps the parenthesized
    ///   product as one component. Every component is read as a value type, or
    ///   a computation type for the lazy product, under the chain's frame, in
    ///   written order, and the former is planned over them; the inner links of
    ///   the chain are not read.
    /// - provides: the eager product, the sum and the lazy product of the
    ///   fragment, each the same core type as the braced `#{A, B}`, `+{A, B}`
    ///   and `&{C, D}`.
    /// - fails: yields the wrong-sort refusal where no type of the former's
    ///   sort is read, and the refusal of any link of the chain out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The chain's refusal.
    ///
    /// # Termination
    /// Each round of the chain walk consumes fuel and replaces one link of the
    /// finite tree by its two operands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product and a sum of atoms, a chain of three of
    ///   each and of the lazy product, a parenthesized inner product, a product
    ///   inside a sum and a product where a computation type is read, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal.
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_lazy_record_lowers_to_one_lazy_product`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::Product(components) | Plan::Sum(components, _) | Plan::With(components, _))) if self.cx().operands.read(components).len() >= 2_usize
                )
        },
    )]
    fn chain(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        former: Former,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let lazy = former == Former::LazyProductType;
        let frame = self.require(
            site,
            if lazy {
                Produced::CompType
            }
            else {
                Produced::ValueType
            },
        )?;
        let start = self.cx().operands.entries().len();
        let [first, second] = halves(site, &mut cursor, former)?;
        let mut pending = Vec::from([second, first]);
        while let Some(operand) = pending.pop() {
            match self
                .cx_mut()
                .fuel
                .spend()
                .and_then(|()| self.chained(site, operand, former))
            {
                Ok(Some([inner_first, inner_second])) => {
                    pending.extend([inner_second, inner_first]);
                },
                Ok(None) => {
                    let _key = self.cx_mut().operands.push(operand);
                },
                Err(refusal) => {
                    self.cx_mut().operands.truncate(At::from(start));
                    return Err(refusal);
                },
            }
        }
        let components = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        for position in components.start .. components.end {
            if let Some(&component) = self.cx().operands.entries().get(position) {
                self.read(
                    component,
                    if lazy {
                        Reading::CompType(frame)
                    }
                    else {
                        Reading::ValueType(frame)
                    },
                );
            }
        }
        // A chain writes no label.
        let (components, unlabelled) = (self.cx().kept(components), FormStretch::default());
        let plan = if lazy {
            Plan::With(components, unlabelled)
        }
        else if former == Former::SumType {
            Plan::Sum(components, unlabelled)
        }
        else {
            Plan::Product(components)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// The two operands of `operand` when it is an unparenthesized form of
    /// `former`, a link of the chain a form of `former` heads.
    ///
    /// # Specification
    /// - requires: `operand` is an operand of a chain of `former` at `site`.
    /// - ensures: a form of `former` answers its operands in written order; any
    ///   other node, a parenthesized one of `former` included, answers nothing.
    /// - provides: the one place a product or a sum chain is followed.
    /// - fails: a repaired or ill-shaped link in the chain yields its own
    ///   refusal; [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The inner link's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three and a parenthesized inner product
    ///   separate the followed link from the kept component, and a product
    ///   inside a sum is kept as one summand.
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |halves| halves.is_none_or(|[first, second]| first != operand && second != operand)))]
    #[inline]
    pub fn chained(
        &mut self,
        site: Site,
        operand: NodeIndex,
        former: Former,
    ) -> Result<Option<[NodeIndex; 2]>, LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(operand)
        else {
            return Ok(None);
        };
        let Shape::Form { name, former: link } = shape_of(self.cx().pbg, node)?
        else {
            return Ok(None);
        };
        if link != former {
            return Ok(None);
        }
        let link = Site {
            at: Placed::of(operand, node),
            name,
            reading: site.reading,
        };
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let read =
            read_pieces(self.cx().pbg, self.cx().tree, operand, &mut scratch).and_then(|()| {
                if let Maybe::Present(repaired) = scratch.repair {
                    return Err(repaired.refusal(name));
                }
                halves(
                    link,
                    &mut Cursor::new(&scratch.pieces, link.at.span),
                    former,
                )
            });
        self.cx_mut().scratch = scratch;

        read.map(Some)
    }

    /// Plan the box from `domain` to `codomain`: the thunked flat arrow a
    /// function value has.
    ///
    /// # Specification
    /// - requires: `site` stands as a value type under `frame`; `domain` and
    ///   `codomain` are its operands.
    /// - ensures: a domain list naming a binder, `(x : A, …) -> B`, is the
    ///   telescope; else its domains — each member of a parenthesised list,
    ///   none for `()`, else the one operand there — are each read as value
    ///   types under `frame`, its codomain as
    ///   [`Self::box_output`](crate::lower::Expressions::box_output) reads it,
    ///   and it is planned as the thunked arrow over them.
    /// - provides: the one reading of the box `->`.
    /// - fails: either hole's own refusal, and a domain list's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The box's refusal.
    ///
    /// # Termination
    /// The domain loop runs once per entry of the finite domain stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arrow`].
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&(Plan::ValueFunction(..) | Plan::Telescope(..)))
                )
        },
    )]
    fn boxed(
        &mut self,
        site: Site,
        frame: Frame,
        domain: Placed,
        codomain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if Models::new(self.host()).telescope_function(site, frame, domain, codomain)?
            == arity::Planned(true)
        {
            return Ok(());
        }
        let start = self.cx().operands.entries().len();
        if let Err(refusal) = self.domains(domain) {
            self.cx_mut().operands.truncate(At::from(start));
            return Err(refusal);
        }
        let domains = Stretch {
            start,
            end: self.cx().operands.entries().len(),
        };
        for position in domains.start .. domains.end {
            if let Some(&each) = self.cx().operands.entries().get(position) {
                self.read(each, Reading::ValueType(frame));
            }
        }
        let output = self.box_output(codomain, frame)?;
        self.read(codomain.node, output);

        self.plan(
            site,
            Plan::ValueFunction(self.cx().kept(domains), codomain.node),
        );

        Ok(())
    }

    /// How a box reads its output `codomain` under `frame`: a group of
    /// outputs, `(q : A, r : B)` or `()`, and a row before a type, `[E] B`, as
    /// a definition's result is read; any other output as a value type, the
    /// returner inserted when the box is minted.
    ///
    /// # Specification
    /// - requires: nothing beyond a well-formed tree.
    /// - ensures: [`Reading::Result`] under `frame` for a written group, as
    ///   `Models::written_group` reads it, and for a returner type whose first
    ///   piece is `[`; [`Reading::ValueType`] under `frame` otherwise, so a
    ///   written computation type such as `-F B` is refused as a value type and
    ///   a staged box `A -> (B -> C)` keeps its output a box.
    /// - fails: the group's refusal; [`LoweringRefusal::UnknownMold`] for a
    ///   foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// As `Models::written_group`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a box returning a group, one under a row, a plain
    ///   output and a written returner.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_box_returns_a_group_under_a_row_4853`
    /// - witness: `gandr-surface-lowering::lower::tests::a_computation_codomain_of_a_box_is_refused`
    #[spec(ensures: |ret| matches!(ret, Err(_) | Ok(Reading::Result(_) | Reading::ValueType(_))))]
    #[inline]
    pub fn box_output(
        &mut self,
        codomain: Placed,
        frame: Frame,
    ) -> Result<Reading, LoweringRefusal<'source>>
    {
        let rowed = if matches!(
            self.cx().form_at(codomain)?,
            Some((_, Former::ReturnerType))
        ) {
            let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
            let read =
                read_pieces(self.cx().pbg, self.cx().tree, codomain.node, &mut scratch).map(|()| {
                    matches!(
                        scratch.pieces.first(),
                        Some(&Piece::Tile { label, .. }) if label == TileName::BRACKET_OPEN
                    )
                });
            self.cx_mut().scratch = scratch;
            read?
        }
        else {
            false
        };
        if rowed || Models::new(self.host()).written_group(codomain, frame)?.0 {
            return Ok(Reading::Result(frame));
        }

        Ok(Reading::ValueType(frame))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The computation type a box returns, its output `codomain` minted: the
    /// returner of a value type, and a group or a rowed returner as it stands.
    ///
    /// # Specification
    /// - requires: `codomain` is minted or absent.
    /// - ensures: `-F B` for an output minted as the value type `B`, with the
    ///   box's origin; the computation type an output read as a result minted.
    /// - fails: the output's absence; the other-sort absence for an output
    ///   minted as neither.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::box_output`](crate::lower::Expressions::box_output).
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_box_returns_a_group_under_a_row_4853`
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) => sink.arena.comp_type(id).is_some(),
        | Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn box_returns(
        &self,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        match self.cx().lowered_at(codomain) {
            Maybe::Present(Lowered::ValueType(returned)) => {
                let id = sink.arena.comp_type_returner(returned);
                sink.origins.record_comp_type(id, origin);
                Maybe::Present(id)
            },
            Maybe::Present(Lowered::CompType(id)) => Maybe::Present(id),
            Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Append the domains a value function space's domain operand writes to
    /// the operand store.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before the box's `->`.
    /// - ensures: nothing for the empty list `()`, so `() -> C` takes no
    ///   argument; each member of an unrepaired parenthesised list of more than
    ///   one, left to right; else `domain` itself, whose own reading groups or
    ///   reports a repair.
    /// - provides: the n-ary domain of the box, the one place a type list is
    ///   read.
    /// - fails: yields the list's refusal for a member out of shape;
    ///   [`LoweringRefusal::UnknownMold`] for a mold the grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The list's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no domain, one domain and a list of two, each
    ///   asserted through the alias it lowers.
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        captures: before = self.cx().operands.entries().len(),
        ensures: |ret| ret.is_err() || self.cx().operands.entries().len() >= before,
    )]
    #[inline]
    pub fn domains(
        &mut self,
        domain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(domain.node)
        else {
            self.cx_mut().operands.push(domain.node);
            return Ok(());
        };
        let Shape::Form {
            name,
            former: Former::ParenthesizedType,
        } = shape_of(self.cx().pbg, node)?
        else {
            self.cx_mut().operands.push(domain.node);
            return Ok(());
        };
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let read = read_pieces(self.cx().pbg, self.cx().tree, domain.node, &mut scratch);
        let listed = read.and_then(|()| {
            let commas = scratch.pieces.iter().any(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::COMMA),
            );
            let empty = !scratch
                .pieces
                .iter()
                .any(|piece| matches!(*piece, Piece::Operand(_)));
            if empty && let Maybe::Absent(_) = scratch.repair {
                Ok(())
            }
            else if commas && let Maybe::Absent(_) = scratch.repair {
                let list = Site {
                    at: domain,
                    name,
                    reading: Reading::Unread,
                };
                arguments(
                    list,
                    &mut Cursor::new(&scratch.pieces, domain.span),
                    &mut self.cx_mut().operands,
                )
            }
            else {
                self.cx_mut().operands.push(domain.node);
                Ok(())
            }
        });
        self.cx_mut().scratch = scratch;

        listed
    }

    /// Whether the lambda at `site` stands where a static former is read, and
    /// the static classifier its position states when it states one.
    ///
    /// # Specification
    /// - requires: `site` is a lambda.
    /// - ensures: `Some` with the classifier
    ///   [`Context::static_lambdas`](gandr_surface_lowering_base::lower::Context::static_lambdas)
    ///   files for a lambda filed there; `Some` with the written type for a
    ///   definition's body whose signature, and for an argument whose
    ///   parameter's written type, is a static arrow `K -> J`
    ///   ([`Self::static_arrow`]); `None` for any other lambda, one a thunked
    ///   arrow or the alias answers among them.
    /// - fails: as `Native::unwrapped`.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a motive, a signed definition's body and the body
    ///   nested in it, and an argument at a parameter of a static classifier
    ///   each lower as a static lambda, and a lambda the alias answers lowers
    ///   as a dynamic one.
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_s_position_decides_its_sort_4508`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none() || self.cx().static_lambdas.contains_key(&site.at.node) || self.cx().inherited.contains_key(&site.at.node) || self.cx().parameter_typed.contains_key(&site.at.node)))]
    fn static_at(
        &mut self,
        site: Site,
    ) -> Result<Option<Maybe<NodeIndex, classified::Absent>>, LoweringRefusal<'source>>
    {
        if let Some(&classifier) = self.cx().static_lambdas.get(&site.at.node) {
            return Ok(Some(classifier));
        }
        let stated = match (
            self.cx().inherited.get(&site.at.node),
            self.cx().parameter_typed.get(&site.at.node),
        ) {
            (Some(&native::Classifier::Written(signature)), _) => signature,
            (_, Some(called)) => called.typed.node,
            _ => return Ok(None),
        };
        Ok(self.static_arrow(stated)?.map(|_| Maybe::Present(stated)))
    }

    /// The domain and the codomain of `classifier` when it is a static arrow:
    /// its parentheses stripped, an arrow `K -> J` of two operands that is no
    /// box, the classifier of a type operator where a value type is written.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arrow's two operands for an arrow that
    ///   [`crate::form::writes_box`] does not read as a box; nothing for any
    ///   other form, a thunked arrow `+U (A -> -F B)` and the box `A -> B`
    ///   among them.
    /// - fails: as `Native::unwrapped`.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::static_at`].
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_s_position_decides_its_sort_4508`
    /// - witness: `gandr-surface-lowering::lower::tests::a_box_passes_a_lambda_applies_states_a_motive_and_matches_its_columns_4853`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |arrow| arrow.is_none_or(|(domain, codomain)| domain != codomain)))]
    fn static_arrow(
        &mut self,
        classifier: NodeIndex,
    ) -> Result<Option<(NodeIndex, NodeIndex)>, LoweringRefusal<'source>>
    {
        let Maybe::Present(native::Unwrapped {
            node: written,
            former: Former::ArrowType,
            ref operands,
            ..
        }) = Native::new(self.host()).unwrapped(classifier)?
        else {
            return Ok(None);
        };
        let &[domain, codomain] = operands.as_slice()
        else {
            return Ok(None);
        };
        // A box's argument is a function value, never a type operator.
        if self.boxes(written)?.0 {
            return Ok(None);
        }
        Ok(Some((domain, codomain)))
    }

    /// Mark each telescope type written as an argument of a call of
    /// `resolved` at a parameter whose written type is no universe: there it
    /// is the tuple of its entries, not the quote of their product (#5390),
    /// as at a constructor's field (#5208).
    ///
    /// # Specification
    /// - requires: `arguments` holds positions of the operand store, the call's
    ///   arguments from left to right, its first list's before its second's.
    /// - ensures: an argument written as a telescope type, bare or inside
    ///   parentheses as `Native::written_telescope` reads it, joins
    ///   [`Context::valued_telescopes`](gandr_surface_lowering_base::lower::Context::valued_telescopes)
    ///   with the parameter's written type when that type holds a value, as
    ///   `Native::held_at` reads it. The parameters are, in order, those
    ///   [`Self::listed_parameters`] reads and then the domains of each arrow
    ///   of the type after them. An argument past the parameters the walk
    ///   reads, or at a parameter written with no type, stays as it is. No walk
    ///   runs when no argument is a telescope type or a parenthesised type.
    /// - provides: the reading of a telescope type written as an argument of a
    ///   call in a type.
    /// - fails: as `Native::unwrapped`.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Termination
    /// The loop runs once per argument of the finite stretch `arguments`, and
    /// each arrow it reads steps to the arrow's codomain, strictly deeper in a
    /// finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope argument at a product parameter, at a
    ///   `Type` parameter and at the domain of a function's result, and one
    ///   inside parentheses, each asserted as the exact core value.
    /// - witness: `gandr-surface-lowering::lower::tests::a_telescope_argument_of_a_call_in_a_type_reads_by_its_parameter_5390`
    /// - witness: `gandr-surface-lowering::lower::tests::a_parenthesised_or_nested_telescope_reads_by_its_place_5500`
    #[spec(
        captures: before = self.cx().valued_telescopes.len(),
        ensures: |ret| ret.is_err() || self.cx().valued_telescopes.len() >= before,
    )]
    fn valued_arguments(
        &mut self,
        resolved: Resolved,
        arguments: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // Only a telescope type or parentheses around one write a telescope.
        let written = |lowerer: &Self, position: usize| {
            lowerer
                .cx()
                .operands
                .entries()
                .get(position)
                .and_then(|&argument| lowerer.cx().tree.node(argument))
                .is_some_and(|node| {
                    matches!(
                        shape_of(lowerer.cx().pbg, node),
                        Ok(Shape::Form {
                            former: Former::TelescopeType | Former::ParenthesizedType,
                            ..
                        })
                    )
                })
        };
        if !(arguments.start .. arguments.end).any(|position| written(self, position)) {
            return Ok(());
        }
        let (listed, mut rest) = self.listed_parameters(resolved)?;
        let mut listed = listed.into_iter();
        let mut domains: Vec<NodeIndex> = Vec::new();
        let mut domain = 0_usize;
        for position in arguments.start .. arguments.end {
            let parameter = if let Some(parameter) = listed.next() {
                parameter
            }
            else {
                if domain >= domains.len() {
                    let Some(arrow) = rest
                    else {
                        break;
                    };
                    let Maybe::Present(native::Unwrapped {
                        former: Former::ArrowType,
                        operands,
                        ..
                    }) = Native::new(self.host()).unwrapped(arrow)?
                    else {
                        break;
                    };
                    let Some((&codomain, written)) = operands.split_last()
                    else {
                        break;
                    };
                    domains.clear();
                    domains.extend_from_slice(written);
                    domain = 0_usize;
                    rest = Some(codomain);
                }
                let parameter = domains.get(domain).copied();
                domain = domain.saturating_add(1_usize);
                parameter
            };
            if written(self, position)
                && let Some(&argument) = self.cx().operands.entries().get(position)
                && let Some(telescope) = Native::new(self.host()).written_telescope(argument)?
                && let Some(parameter) = parameter
                && let native::Holds::Value(stated) = Native::new(self.host()).held_at(parameter)?
            {
                let _first = self.cx_mut().valued_telescopes.insert(telescope, stated);
            }
        }

        Ok(())
    }

    /// The written type of each parameter a call of `resolved` meets in the
    /// head's own parameter list, and the type that stands after them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a head declared at a written type, no listed parameter
    ///   and that type. For a declaration a function tail defines, the type of
    ///   each name its parameter list binds, in order, absent for a name
    ///   written with no type and shared by names written before one type, `m n
    ///   : T`, and the result type written after the list's arrow. For every
    ///   other head, nothing.
    /// - provides: [`Self::valued_arguments`]'s parameters.
    /// - fails: a fault reading the function form's pieces.
    /// - panics: none.
    /// - executable: none — a predicate restating the answer would read the
    ///   function form's syntax again.
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::valued_arguments`].
    /// - witness: `gandr-surface-lowering::lower::tests::a_telescope_argument_of_a_call_in_a_type_reads_by_its_parameter_5390`
    fn listed_parameters(
        &mut self,
        resolved: Resolved,
    ) -> Result<(Vec<Option<NodeIndex>>, Option<NodeIndex>), LoweringRefusal<'source>>
    {
        let constant = match resolved {
            Resolved::Binder(bound) => {
                return Ok((Vec::new(), match bound.declared {
                    Maybe::Present(written) => Some(written),
                    Maybe::Absent(_) => None,
                }));
            },
            Resolved::Declaration {
                declared: Maybe::Present(written),
                ..
            } => return Ok((Vec::new(), Some(written))),
            Resolved::Declaration { constant, .. } => constant,
        };
        let Some(Maybe::Present(Half {
            declaration,
            operand: Operand::Function,
            ..
        })) = self
            .cx()
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return Ok((Vec::new(), None));
        };
        let mut scratch = core::mem::take(&mut self.cx_mut().scratch);
        let read = read_pieces(
            self.cx().pbg,
            self.cx().tree,
            declaration.node,
            &mut scratch,
        );
        let mut types: Vec<Option<NodeIndex>> = Vec::new();
        let mut result = None;
        // Where the parameter being read starts: names that share a type,
        // `m n : T`, each take it.
        let mut group = 0_usize;
        let mut place = HeaderAt::Head;
        for piece in &scratch.pieces {
            match (place, *piece) {
                (HeaderAt::Head, Piece::Tile { label, .. }) if label == TileName::PAREN_OPEN => {
                    place = HeaderAt::Listed;
                },
                (HeaderAt::Listed, Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    place = HeaderAt::Closed;
                },
                (HeaderAt::Listed, Piece::Tile { label, .. })
                    if TileName::BINDERS.contains(&label) =>
                {
                    types.push(None);
                },
                (HeaderAt::Listed, Piece::Tile { label, .. }) if label == TileName::COMMA => {
                    group = types.len();
                },
                (HeaderAt::Listed, Piece::Operand(operand)) => {
                    for typed in types.iter_mut().skip(group) {
                        *typed = Some(operand.node);
                    }
                },
                (HeaderAt::Closed, Piece::Tile { label, .. }) if label == TileName::ARROW => {
                    place = HeaderAt::Arrow;
                },
                (HeaderAt::Arrow, Piece::Operand(operand)) => {
                    result = Some(operand.node);
                    break;
                },
                (HeaderAt::Closed | HeaderAt::Arrow, _) => break,
                (HeaderAt::Head | HeaderAt::Listed, _) => {},
            }
        }
        self.cx_mut().scratch = scratch;
        read?;

        Ok((types, result))
    }

    /// Classify a static lambda, `fun (A) { T }`: a lambda whose position
    /// reads it as a type operator ([`Self::static_at`]), over `classifier`
    /// when the position states one.
    ///
    /// # Specification
    /// - requires: `site` is a lambda [`Self::static_at`] answers with
    ///   `classifier`.
    /// - ensures: the lambda binds its one name in a frame extending its own,
    ///   untyped — the checker reads the type from the operator's classifier —
    ///   reads the one operand its block holds as a value under that frame, so
    ///   a type written there is quoted, and is planned as the static lambda
    ///   over it. The body is filed in
    ///   [`Context::static_bodies`](gandr_surface_lowering_base::lower::Context::static_bodies),
    ///   so a dynamic call written there is the type of the code it returns
    ///   (#3786). Where the classifier's codomain is itself a static arrow, the
    ///   body is filed in
    ///   [`Context::static_lambdas`](gandr_surface_lowering_base::lower::Context::static_lambdas)
    ///   with it, so a lambda written there is static too. A transport's motive
    ///   [`Context::over_points`](gandr_surface_lowering_base::lower::Context::over_points)
    ///   records keeps its binder untyped, and records it with the carrier of
    ///   its path (#3773).
    /// - provides: the introduction of a type operator.
    /// - fails: yields the wrong-sort refusal where no value is read, and for a
    ///   block holding a statement, at the block; the arity refusal for a
    ///   binder count other than one; the unadmitted refusal for a type
    ///   abstraction; a misplaced-tile fault for a binder out of shape or
    ///   typed; the binder policy's refusal; and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one static lambda, two nested whose body names both
    ///   binders, a static lambda where a value type is read, two binders and a
    ///   statement, each asserted as the exact core node read back out of the
    ///   arena or the exact refusal; a lowercase binder name; a body calling a
    ///   binder that holds a family.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_a_lowercase_name`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_transport_moves_through_a_family_a_parameter_names_3786`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.cx().plans.get(site.at.node),
                    Some(&Plan::StaticLambda(_))
                )
        },
    )]
    fn static_lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        classifier: Maybe<NodeIndex, classified::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        closed(site, &mut cursor, TileName::FUN)?;
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(
                FormName::TYPE_ABSTRACTION,
                FragmentBoundary::Unadmitted(Unbuilt::TypeAbstraction),
            ));
        }
        closed(site, &mut cursor, TileName::PAREN_OPEN)?;
        let binder = match cursor.peek() {
            Maybe::Present(Piece::Tile { label, at })
                if label == TileName::IDENTIFIER
                    || label == TileName::TYPE_IDENTIFIER
                    || label == TileName::TYPE_VARIABLE =>
            {
                let _binder = cursor.tile(label);
                at
            },
            Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        // A type operator abstracts one type; a curried one nests.
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            let mut ahead = cursor.clone();
            let mut count = 1_usize;
            while let Maybe::Present(_) = ahead.tile(TileName::COMMA) {
                count = count.saturating_add(1_usize);
                let _next = ahead.read();
            }
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        let Maybe::Present(open) = cursor.tile(TileName::BRACE_OPEN)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        // The block holds the body alone: a statement has no reading in a
        // type.
        let statement = Site {
            at: Placed {
                node: site.at.node,
                span: ByteSpan::new(open.span.start(), site.at.span.end()).unwrap_or(site.at.span),
            },
            name: FormName::BLOCK,
            reading: Reading::Value(frame),
        };
        let Run::One(body) = cursor.operands()
        else {
            return Err(statement.out(FragmentBoundary::WrongSort));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            return Err(statement.out(FragmentBoundary::WrongSort));
        }
        exhausted(site, &cursor)?;
        let name = self.cx().name_at(binder);
        self.note_binder(binder, frame, name)?;
        let extended = self
            .cx_mut()
            .scope
            .extend_operand(frame, name, Maybe::Present(binder.span));
        // A transport's motive ranges over its path's points (#3773).
        if let Some(&carrier) = self.cx().over_points.get(&site.at.node) {
            let _first = self.cx_mut().binders_over_points.insert(extended, carrier);
        }
        if let Maybe::Present(classifier) = classifier
            && let Some((_, codomain)) = self.static_arrow(classifier)?
            && self.static_arrow(codomain)?.is_some()
        {
            let _first = self
                .cx_mut()
                .static_lambdas
                .insert(body.node, Maybe::Present(codomain));
        }
        let _body = self.cx_mut().static_bodies.insert(body.node);
        self.cx_mut().static_spans.push(body.span);
        self.read(body.node, Reading::Value(Frame::Inner(extended)));

        self.plan(site, Plan::StaticLambda(body.node));

        Ok(())
    }

    /// Classify a parenthesised type, `(T)`, a function's group of outputs
    /// where a result is read, or, where a value is read, the annotation `(v :
    /// T)` the type grammar molds as one.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised type.
    /// - ensures: where a result is read, a group of no entry, of several, or
    ///   of one labelled entry is the outputs, as `Models::output_group` reads
    ///   them; otherwise the one operand is read at the form's own reading and
    ///   adopted; where a value is read, a `:` after the operand makes the form
    ///   the annotation of that operand, read as `Native::annotated` reads the
    ///   expression grammar's, so a type-valued call's argument takes the
    ///   spelling a path's endpoint takes.
    /// - provides: grouping in type position, a function's outputs, and the
    ///   annotated argument of a type-valued call.
    /// - fails: yields the empty-list refusal for `()` where no result is read,
    ///   which is never the unit type, the hole's own refusal, a misplaced-tile
    ///   fault at the first comma of a list, which only a value function
    ///   space's domain and a result read, and at a `:` where no value is read,
    ///   and the annotation's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parenthesized type operands keep the surrounding
    ///   reading and lower to the wrapped type rather than introducing a core
    ///   constructor; empty parentheses are refused by name; a result's group
    ///   of outputs lowers to the many-value returner.
    /// - witness: `gandr-surface-lowering::lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `gandr-surface-lowering::lower::tests::the_empty_parentheses_are_never_the_unit`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_type_valued_calls_argument_takes_an_annotation_3633`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_group_of_outputs_is_the_many_value_returner`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.cx().plans.get(site.at.node), Some(&Plan::Transparent(child)) if self.cx().reading(child) == site.reading)
                || (matches!(site.reading, Reading::Value(_))
                    && matches!(self.cx().plans.get(site.at.node), Some(&(Plan::Transparent(_) | Plan::Ascribed(..)))))
                || (matches!(site.reading, Reading::Result(_))
                    && matches!(self.cx().plans.get(site.at.node), Some(&Plan::Returns(_))))
        },
    )]
    fn parenthesized_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::PAREN_OPEN);
        // A group written as a function's result is its outputs, as the group
        // before an arrow is its inputs: `-> (q : Nat, r : Nat)`, `-> ()`.
        if let Reading::Result(frame) = site.reading
            && Models::new(self.host()).output_group(site, frame)? == arity::Planned(true)
        {
            return Ok(());
        }
        let run = cursor.operands();
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        if matches!(site.reading, Reading::Value(_))
            && let Maybe::Present(_) = cursor.at(TileName::COLON)
        {
            return Native::new(self.host()).annotated(site, run, cursor);
        }
        let inner = site.one(run)?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        self.group(site, inner);
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Read `position` as `reading`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied reading without resizing
    ///   the table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures, definitions and nested binder bodies
    ///   receive their own expected sorts and frames.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    #[spec(
        captures: count = usize::from(self.cx().readings.count()),
        ensures: |_| {
            usize::from(self.cx().readings.count()) == count
                && self
                    .cx().readings
                    .get(position)
                    .is_none_or(|held| *held == reading)
        },
    )]
    #[inline]
    pub fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    )
    {
        if let Some(held) = self.cx_mut().readings.get_mut(position) {
            *held = reading;
        }
        // A value a type reads — a type-position call's argument — stands in
        // that type's telescope, which the enclosing type carries as a whole.
        if let (Reading::Value(_), Family::Type) = (reading, self.cx().reader.family()) {
            let _first = self.cx_mut().type_read.insert(position);
        }
    }

    /// Record `plan` for the form at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied plan without resizing the
    ///   table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literals, applications and quoted types preserve
    ///   their planned former through the minting sweep; their concrete
    ///   operands are checked by the consumer witnesses rather than copied into
    ///   a snapshot.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_where_a_value_is_read_is_quoted`
    #[spec(
        captures: before = (self.cx().plans.count(), core::mem::discriminant(&plan)),
        ensures: |_| {
            self.cx().plans.count() == before.0
                && self
                    .cx().plans
                    .get(site.at.node)
                    .is_none_or(|held| core::mem::discriminant(held) == before.1)
        },
    )]
    #[inline]
    pub fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    )
    {
        if let Some(held) = self.cx_mut().plans.get_mut(site.at.node) {
            *held = plan;
        }
    }

    /// Plan the form at `site` as `plan`, a head applied to the arguments
    /// `read` holds, each read as a value in `frame`.
    ///
    /// A decode, an unquote and a reapplication read their arguments inside
    /// the type they make, so each argument counts in that type's telescope,
    /// as a family's arguments do. A lambda among them reads its body inside
    /// the type too. Each planner of an application marks its arguments here.
    ///
    /// # Specification
    /// - requires: `read` holds the arguments of `plan` in the operand store.
    /// - ensures: each argument of `read` is read as a value in `frame`, and
    ///   counts among the values a type reads when `plan` is a decode, an
    ///   unquote or a reapplication; `site` takes `plan`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses restate [`Self::read`] and
    ///   [`Self::plan`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function to a universe unquoted where a type is
    ///   read, a lambda in a type-valued call's argument and a descent's
    ///   unquote each read their arguments inside the type.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_to_a_universe_unquotes_where_a_type_is_read`
    /// - witness: `gandr-surface-lowering::lower::tests::a_lambda_in_a_type_valued_call_reads_outer_variables_at_their_indices_3616`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    #[inline]
    pub fn plan_applied(
        &mut self,
        site: Site,
        plan: Plan,
        read: Stretch,
        frame: Frame,
    )
    {
        for position in read.start .. read.end {
            if let Some(&argument) = self.cx().operands.entries().get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        let cx = self.cx_mut();
        if matches!(
            plan,
            Plan::Decode(..) | Plan::Unquote(..) | Plan::Reapplied(..)
        ) {
            cx.in_type
                .extend(stretch(cx.operands.entries(), read).iter().copied());
        }
        self.plan(site, plan);
    }

    /// The name of the hole written at `at`: its form's group, and its place
    /// among the group's holes in the order the text writes them. A hole
    /// keeps its name however the text around it is spelled or laid out, and
    /// whatever another declaration writes.
    ///
    /// # Specification
    /// - requires: `at` is a hole of the tree.
    /// - ensures: each hole is named by its form's group and by how many holes
    ///   the group writes before it, so distinct holes have distinct names.
    /// - fails: the budget refusal for a group or a place past the written
    ///   names' bits ([`gandr_core_term::hole::HoleId::written`]).
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — holes before, between and after other declarations,
    ///   in a pattern and in a body, each named by its written place; a form's
    ///   holes keep their names when another form writes more, and when another
    ///   declaration is written in one form or in two.
    /// - witness: `gandr-surface-lowering::lower::tests::source_holes_keep_their_families_and_distinct_occurrences`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_form_s_holes_keep_their_names_when_another_form_writes_more_5598`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_declaration_in_one_form_or_two_names_the_later_holes_alike_5469`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&hole| {
        let block = self.cx().form_of(at.node);
        self.cx().hole_groups.groups.get(usize::from(block)).is_some_and(|&(number, first_block)| {
            let first = self.cx().holes.partition_point(|&(held, ..)| held < first_block);
            self.cx().holes.binary_search(&(block, at.span.start(), at.node)).is_ok_and(|held| {
                u32::try_from(held.saturating_sub(first)).ok().and_then(|place| {
                    gandr_core_term::hole::HoleId::written(
                        gandr_core_term::hole::HoleForm::from(number),
                        gandr_core_term::hole::HolePlace::from(place),
                    )
                }) == Some(hole)
            })
        })
    }))]
    #[inline]
    pub fn hole(
        &mut self,
        at: Placed,
    ) -> Result<gandr_core_term::hole::HoleId, LoweringRefusal<'source>>
    {
        if self.cx().holes.is_empty() {
            self.read_holes(LayoutBlock::from(0_usize));
        }
        let exceeded = LoweringRefusal::BudgetExceeded {
            budget: self.cx().fuel.budget(),
        };
        let block = self.cx().form_of(at.node);
        let (form, first_block) = self.hole_group(block);
        let held = self
            .cx()
            .holes
            .binary_search(&(block, at.span.start(), at.node))
            .map_err(|_absent| exceeded)?;
        let first = self
            .cx()
            .holes
            .partition_point(|&(read, ..)| read < first_block);
        let place = u32::try_from(held.saturating_sub(first)).map_err(|_overflow| exceeded)?;
        gandr_core_term::hole::HoleId::written(form, gandr_core_term::hole::HolePlace::from(place))
            .ok_or(exceeded)
    }

    /// The group of the layout block `block`: the number a hole's name holds
    /// for the block, and the group's first block. A block that holds a
    /// top-level form joins the group of the block before it when one slot
    /// owns both forms, as a signature and its definition, or a declaration
    /// and its attributes. A block that holds a root joins the group before
    /// it, and the first block after the leading roots joins their group.
    /// Thus a tree joined after a closure numbers its groups as the parse of
    /// its whole text does. Each other block opens the next group, so a
    /// rewrite that writes a declaration in one form or in two renames no
    /// hole of another declaration (#5469).
    ///
    /// # Specification
    /// - requires: the slot of each top-level form up to `block` is collected.
    /// - ensures: the groups of the blocks up to `block` are held in
    ///   [`Context::hole_groups`](gandr_surface_lowering_base::lower::Context::hole_groups),
    ///   one for each block; the group of `block`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration written in one form or in two names the
    ///   holes of the declaration after it alike; a block that holds
    ///   documentation, and no form, opens a group of its own; a document
    ///   resumed after its closure names its holes as the whole text does.
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_declaration_in_one_form_or_two_names_the_later_holes_alike_5469`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: |ret| self.cx().hole_groups.groups.len() > usize::from(block)
        && ret.0 == gandr_core_term::hole::HoleForm::from(self.cx().hole_groups.groups.get(usize::from(block)).map_or(u32::MAX, |&(number, _)| number)))]
    #[inline]
    pub fn hole_group(
        &mut self,
        block: LayoutBlock,
    ) -> (gandr_core_term::hole::HoleForm, LayoutBlock)
    {
        let tree = self.cx().tree;
        let roots = tree.roots();
        let forms = tree.forms();
        while self.cx().hole_groups.groups.len() <= usize::from(block) {
            let next = LayoutBlock::from(self.cx().hole_groups.groups.len());
            let earlier = roots.partition_point(|root| root.block() < next);
            let group = if roots.get(earlier).is_some_and(|root| root.block() == next) {
                self.cx()
                    .hole_groups
                    .groups
                    .last()
                    .copied()
                    .unwrap_or((0, next))
            }
            else {
                while forms
                    .get(self.cx().hole_groups.form)
                    .is_some_and(|&form| self.cx().form_of(form) < next)
                {
                    self.cx_mut().hole_groups.form = self.cx().hole_groups.form.saturating_add(1);
                }
                let owner = forms
                    .get(self.cx().hole_groups.form)
                    .filter(|&&form| self.cx().form_of(form) == next)
                    .and_then(|&form| match self.cx().collected.owner_of(form) {
                        Maybe::Present(slot) => Some(slot),
                        Maybe::Absent(_) => None,
                    });
                // Only roots lie before the block: it joins their group.
                let leading = earlier == usize::from(next);
                let joined = leading || (owner.is_some() && owner == self.cx().hole_groups.owner);
                self.cx_mut().hole_groups.owner = owner;
                match (joined, self.cx().hole_groups.groups.last()) {
                    (true, Some(&previous)) => previous,
                    (_, Some(&(number, _))) => (number.saturating_add(1), next),
                    (_, None) => (0, next),
                }
            };
            self.cx_mut().hole_groups.groups.push(group);
        }
        self.cx()
            .hole_groups
            .groups
            .get(usize::from(block))
            .map_or_else(
                || (gandr_core_term::hole::HoleForm::from(u32::MAX), block),
                |&(number, first)| (gandr_core_term::hole::HoleForm::from(number), first),
            )
    }

    /// Read the holes among the tree's nodes from block `from` on into the
    /// holes read before, by their form's block, then in the order the text
    /// writes them. The read needs no slot, so a source not yet collected
    /// reads its holes too.
    ///
    /// # Specification
    /// - requires: no node from block `from` on was read before.
    /// - ensures: every hole from block `from` on is held beside its form's
    ///   block, sorted by that block, then by where its text starts, beside the
    ///   holes held before.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::hole`]; a document resumed after a closure
    ///   that read its holes names its own after the closure's.
    /// - witness: `gandr-surface-lowering::lower::tests::source_holes_keep_their_families_and_distinct_occurrences`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body reads every node from block `from` on and sorts the holes once; the check reads each hole once more"
        )
    )]
    #[spec(ensures: self.cx().holes.is_sorted())]
    fn read_holes(
        &mut self,
        from: LayoutBlock,
    )
    {
        for position in self.cx().tree.positions_from(from) {
            let Some(node) = self.cx().tree.node(position)
            else {
                continue;
            };
            if matches!(shape_of(self.cx().pbg, node), Ok(Shape::Form { name, .. }) if name == FormName::HOLE)
            {
                let block = self.cx().form_of(position);
                self.cx_mut()
                    .holes
                    .push((block, node.span().start(), position));
            }
        }
        self.cx_mut().holes.sort_unstable();
    }

    /// The descending sweep: mint every planned node and record its origin.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every type a manifest type component or a type member names
    ///   is minted first, one at a time in source order, each subtree
    ///   descending, so a type head that stands for one adopts a type already
    ///   minted wherever it sits; every functor application is renamed before
    ///   the first of those types written after it, so an instance's manifest
    ///   type is minted before a type naming it; every function result a
    ///   synthesised `cong` reads its codomain off, then every answer type a
    ///   match reads its motive from, then every stated type and declared field
    ///   type a data field read with no answer takes its type from, is minted
    ///   next, the same way, so a `cong` in a type, and a match or a field read
    ///   deeper than the types it reads, find those types minted, and every
    ///   application not yet renamed is renamed. Every other planned node is
    ///   then minted, with its children already minted because the layout puts
    ///   them at strictly higher positions; every minted node gets an origin
    ///   naming the syntax node that produced it, terms and types alike, while
    ///   an adopted child keeps its own. A node whose position bridges its sort
    ///   has the bridge minted over its own core node, with the same syntax
    ///   node's origin marked as inserted. A node under a declaration that
    ///   refused is not minted, and neither is any node above it, unless it
    ///   lies inside an attribute payload or is a type a module signature
    ///   states for it: the side table files a payload whatever its
    ///   declaration's outcome, so an expectation about a refused declaration
    ///   stays readable, and a signature's type is the signature's text, which
    ///   answers for itself. The record type an enclosing signature states a
    ///   nested module at is minted as a root. Last, the body of every witness
    ///   of a member whose member and own type are unrefused is minted as that
    ///   member's constant, its origin the form that stated the second type.
    /// - provides: the whole allocation half of the lowering.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance; nothing else, because every decision was made ascending.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component named before and after its own
    ///   position in the tree, and a witness agreeing and disagreeing with its
    ///   member, each asserted through the checker's verdict.
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body carries out the plan of every node once; the check reads each plan once"
        )
    )]
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || self.cx().plans.iter().all(|(position, plan)| {
                    (self.cx().collected.refused(position).0
                        && !self.shared().in_payload(position).0
                        && !self.shared().stated_apart(position).0)
                        || *plan == Plan::Unplanned
                        || self.cx().taken.get(position) == Some(&true)
                })
        },
    )]
    #[inline]
    pub fn mint(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let from = self.cx().current;
        let owns = |position: &NodeIndex| self.cx().source_of.get(*position) == Some(&from.source);
        let mut stated: Vec<Placed> = self
            .cx().collected
            .structures
            .iter()
            .skip(from.structures)
            .flat_map(|structure| structure.types.iter().chain(&structure.type_members))
            .chain(self.cx().collected.type_members_in(Container::TopLevel(from.source)))
            .filter_map(|component| match component.meaning {
                TypeMeaning::Manifest(defined) => Some(defined),
                TypeMeaning::Sealed | TypeMeaning::Family(_) | TypeMeaning::Instantiated { .. } => {
                    None
                },
            })
            // The record type an enclosing signature states a nested module at
            // is a type that signature writes.
            .chain(
                self.cx().collected
                    .structures
                    .iter()
                    .skip(from.structures)
                    .flat_map(|structure| structure.stated_at.iter().copied()),
            )
            .chain(self.cx().collected.families.iter().skip(from.families).flat_map(|family| {
                family
                    .parameters
                    .iter()
                    .map(|parameter| parameter.classifier)
                    .chain(core::iter::once(family.defined))
            }))
            // A data family's parameter and index types classify the
            // constructors written as its arguments, wherever those stand in
            // the tree (#4027).
            .chain(
                self.cx().argued
                    .iter()
                    .filter(|&(argument, _)| owns(argument))
                    .filter_map(|(_, argued)| self.cx().collected.data.get(argued.form))
                    .flat_map(|form| {
                        form.parameters
                            .iter()
                            .map(|parameter| parameter.classifier)
                            .chain(form.indices.iter().map(|index| index.ty))
                    }),
            )
            // A declaration's parameter types classify the constructors
            // written as the arguments of a call naming it.
            .chain(
                self.cx().parameter_typed
                    .iter()
                    .filter(|&(argument, _)| owns(argument))
                    .map(|(_, declared)| declared.typed),
            )
            // A type a manifest sort is fixed to stands for each reading of
            // the sort off its binder, wherever that reading stands.
            .chain(
                self.cx().fixed_carriers
                    .iter()
                    .filter(|written| owns(&written.node))
                    .copied(),
            )
            // A type a call's omitted model slot fixes a sort to is read when
            // the call files its slot, which the sweep below may reach first
            // (#4403).
            .chain(
                self.cx().planned_models
                    .iter()
                    .filter(|&(call, _)| owns(call))
                    .flat_map(|(_, planned)| {
                        planned
                            .iter()
                            .flat_map(|slot| slot.fixed.iter().map(|&(_, stated)| stated))
                    }),
            )
            .collect();
        stated.sort_unstable_by_key(|defined| (defined.span.start(), defined.node));
        stated.dedup();
        let mut manifests: Vec<NodeIndex> = stated.iter().map(|defined| defined.node).collect();
        manifests.extend(IdentitiesRef::new(self.host_ref()).synthesised_types());
        manifests.extend(
            self.cx()
                .answers
                .iter()
                .filter(|&(position, _)| owns(position))
                .map(|(_, answer)| answer.node),
        );
        // A type stated for a constructor, by an annotation or a typed `let`,
        // classifies it, and the sweep below may reach the constructor first.
        manifests.extend(
            self.cx()
                .classifiers
                .iter()
                .filter(|&(constructor, _)| owns(constructor))
                .map(|(_, &stated)| stated),
        );
        // A constructor answering a definition's application reads the
        // definition's body, which the sweep below reaches after it.
        let mut unfolded = BTreeSet::new();
        for (position, answer) in &self.cx().answers {
            if owns(position) {
                NativeRef::over(self.cx()).unfolded_definitions(answer.node, &mut unfolded);
            }
        }
        manifests.extend(unfolded.into_iter().filter(owns));
        manifests.extend(
            self.cx()
                .inherited
                .iter()
                .filter(|&(position, _)| owns(position))
                .filter_map(|(position, inherited)| match *inherited {
                    native::Classifier::Written(written) => Some(written),
                    // A field's declared type is read where a constructor
                    // classified by it waits for the constructor around it.
                    native::Classifier::Field(native::FieldOf { declared, .. })
                        if self.cx().awaiting.contains(position) =>
                    {
                        Some(declared)
                    },
                    native::Classifier::Field(_)
                    | native::Classifier::Answered { .. }
                    | native::Classifier::Slot(_)
                    | native::Classifier::Parameter(_)
                    | native::Classifier::Stated(_)
                    | native::Classifier::Resulted(_)
                    | native::Classifier::Inserted => None,
                }),
        );
        // A constructor written as an index a generator's result states reads
        // the family's index types and the indices stated before it, which
        // the sweep below reaches after it: those mint first, left to right
        // (#4027).
        manifests.extend(
            self.cx()
                .inherited
                .keys()
                .filter(|&position| owns(position))
                .filter_map(|position| match self.cx().plans.get(*position) {
                    Some(&Plan::Constructor(native::Constructed {
                        classifier: native::Classifier::Stated(stated),
                        ..
                    })) => Some(stated),
                    Some(_) | None => None,
                })
                .filter_map(|stated| {
                    let form = self.cx().collected.data.get(stated.form)?;
                    let generator = form.generators.get(stated.generator)?;
                    Some(
                        form.indices
                            .iter()
                            .take(stated.place.saturating_add(1))
                            .map(|index| index.ty.node)
                            .chain(
                                generator
                                    .indices
                                    .iter()
                                    .take(stated.place.saturating_add(1))
                                    .map(|index| index.node),
                            ),
                    )
                })
                .flatten(),
        );
        // A constructor a `let` with no type binds reads the indices its
        // generator's result states, which mint first (#5050).
        manifests.extend(
            self.cx()
                .inherited
                .keys()
                .filter(|&position| owns(position))
                .filter_map(|position| match self.cx().plans.get(*position) {
                    Some(&Plan::Constructor(native::Constructed {
                        classifier: native::Classifier::Resulted(of),
                        ..
                    })) => Some(of),
                    Some(_) | None => None,
                })
                .filter_map(|of| {
                    let form = self.cx().collected.data.get(of.form)?;
                    let generator = form.generators.get(of.generator)?;
                    Some(generator.indices.iter().map(|index| index.node))
                })
                .flatten(),
        );
        // A field read off a data value by its name, where its position
        // states no answer, reads its type off the value's stated type and the
        // field's declaration.
        manifests.extend(
            self.cx()
                .projected
                .entries()
                .iter()
                .filter_map(native::Projected::typed_by)
                .filter(|&(subject, ..)| owns(&subject))
                .flat_map(|(_, stated, declared)| [stated, declared]),
        );
        // A lambda passed for a parameter whose type names the parameters
        // before it reads the arguments written for them, which the sweep
        // below reaches after the lambda's body (#3921).
        let argued: Vec<NodeIndex> = self
            .cx()
            .argued_binders
            .values()
            .flat_map(|&(called, ..)| self.cx().operands.read(called.applied).iter().copied())
            .filter(|argument| {
                owns(argument) && !self.cx().dependent_answers.contains_key(argument)
            })
            .collect();
        manifests.extend(argued);
        manifests.reverse();
        let mut subtree: Vec<NodeIndex> = Vec::new();
        let mut work: Vec<NodeIndex> = Vec::new();
        while let Some(root) = manifests.pop() {
            if let Some(node) = self.cx().tree.node(root) {
                self.rename_instances_before(Maybe::Present(node.span().start()), sink);
            }
            subtree.clear();
            work.push(root);
            while let Some(position) = work.pop() {
                self.cx_mut().fuel.spend()?;
                subtree.push(position);
                work.extend(self.cx().tree.children(position));
            }
            subtree.sort_unstable_by(|left, right| right.cmp(left));
            for &position in &subtree {
                self.mint_at(position, sink);
            }
        }
        self.rename_instances_before(
            Maybe::Absent(functor::renamed_through::Absent::Everything),
            sink,
        );
        let mut remaining = self.cx().own.len();
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            self.cx_mut().fuel.spend()?;
            let Some(&position) = self.cx().own.get(next)
            else {
                continue;
            };
            self.mint_at(position, sink);
        }
        let cx = self.cx_mut();
        for (position, slot) in cx.collected.slots.iter().enumerate().skip(from.slots) {
            if let Maybe::Present(Half {
                declaration,
                operand: Operand::Member(target),
                ..
            }) = slot.definition
                && let Maybe::Absent(_) = slot.refusal
                && let Some(member) = cx.collected.slots.get(usize::from(target))
                && let Maybe::Absent(_) = member.refusal
                && let Maybe::Present(origin) = cx.origin_at(declaration.node)
            {
                let id = sink.arena.value_constant(member.constant);
                let _minted = sink.value(id, origin);
                let _replaced = cx.witnessed.insert(SlotIndex::from(position), id);
            }
        }
        self.shared().record_labels(sink);
        self.shared().record_covers(sink);
        self.shared().record_framed(sink);

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Record every label planned against an entry that lowered, with what
    /// it names.
    ///
    /// # Specification
    /// - requires: every node is minted or absent.
    /// - ensures: one label per planned site whose entry lowered: a type's at
    ///   the type, with the names of the frames its entry is read under that
    ///   bind in the telescope the type counts its binders in, outermost first;
    ///   a term's at the term.
    /// - fails: never; a site whose entry did not lower records nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record type's, a record's and a dependent arrow's
    ///   labels are each recorded with what they label.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::each_label_names_what_it_labels`
    #[spec(captures: before = sink.origins.labels().len(), ensures: sink.origins.labels().len() <= before.saturating_add(self.cx().labels.len()))]
    fn record_labels(
        &self,
        sink: &mut Sink<'_>,
    )
    {
        let named = |frame: Frame, held: NodeIndex| -> Vec<String> {
            self.cx()
                .scope
                .telescope_names(frame, self.telescope_at(held))
                .into_iter()
                .map(|name| String::from(name.as_ref()))
                .collect()
        };
        for site in self.cx().labels.iter().skip(self.cx().current.labels) {
            let labelled = match site.read {
                LabelRead::ValueType(frame) => match self.cx().value_type_at(site.held) {
                    Maybe::Present(ty) => Labelled::ValueType {
                        ty,
                        context: named(frame, site.held),
                    },
                    Maybe::Absent(_) => continue,
                },
                LabelRead::CompType(frame) => match self.cx().comp_type_at(site.held) {
                    Maybe::Present(ty) => Labelled::CompType {
                        ty,
                        context: named(frame, site.held),
                    },
                    Maybe::Absent(_) => continue,
                },
                LabelRead::Term => match self.cx().value_at(site.held) {
                    Maybe::Present(value) => Labelled::Value(value),
                    Maybe::Absent(_) => continue,
                },
            };
            sink.origins.record_label(Label {
                span: site.written,
                labelled,
            });
        }
    }

    /// Record each prefix minus the current source folded onto a number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each cover whose operator starts in the current source is
    ///   recorded, and no cover of another source is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `-5` records the operator span beside the digit span.
    /// - witness: `gandr-surface-lowering::lower::tests::a_negated_natural_literal_is_one_negative_literal_4732`
    #[spec(captures: before = sink.origins.covers().len(), ensures: sink.origins.covers().len() >= before)]
    fn record_covers(
        &self,
        sink: &mut Sink<'_>,
    )
    {
        for &(operator, operand) in &self.cx().covers {
            if self.cx().collected.unit.source_at(operator.start()) != self.cx().current.source {
                continue;
            }
            sink.origins.record_cover(operator, operand);
        }
    }

    /// Record every type and stated index a data declaration writes with the
    /// names of the binders it is read under.
    ///
    /// # Specification
    /// - requires: every node is minted or absent.
    /// - ensures: one framed span per data site of the current source whose
    ///   node has a span, with the names of the frames its site is read under
    ///   that bind in its telescope, outermost first: the family's parameters,
    ///   then the indices or the constructor's fields before the site.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Cons`'s `S(n)` is framed under the family's
    ///   parameter and the constructor's fields, a field's type under the
    ///   parameter and the fields before it, and an index's type under the
    ///   parameters.
    /// - witness: `gandr-surface-lowering::lower::native::tests::each_data_type_and_stated_index_is_framed_under_its_telescope_931`
    #[spec(captures: before = sink.origins.framed().len(), ensures: sink.origins.framed().len() <= before.saturating_add(self.cx().data_frames.len()))]
    fn record_framed(
        &self,
        sink: &mut Sink<'_>,
    )
    {
        for &(node, frame) in self
            .cx()
            .data_frames
            .iter()
            .skip(self.cx().current.data_frames)
        {
            let Some(span) = self
                .cx()
                .tree
                .node(node)
                .map(gandr_surface_syntax::Node::span)
            else {
                continue;
            };
            let names = self
                .cx()
                .scope
                .telescope_names(frame, self.telescope_at(node))
                .into_iter()
                .map(|name| String::from(name.as_ref()))
                .collect();
            sink.origins.record_framed(span, names);
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Keep the label written at `written` against the entry at `held`, read
    /// as `read`, for
    /// [`Self::record_labels`](crate::lower::ExpressionsRef::record_labels).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn labelled(
        &mut self,
        written: ByteSpan,
        held: NodeIndex,
        read: LabelRead,
    )
    {
        self.cx_mut().labels.push(LabelSite {
            written,
            held,
            read,
        });
    }

    /// Mint the node at `position` by its plan, once.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the node's plan is carried out once, its bridge written over
    ///   it and the result kept as the node's lowered core node; the force over
    ///   the value head of a call of no arguments is that call, so it is minted
    ///   with the call's origin rather than as an insertion at the head; a tail
    ///   whose exit was inferred and minted as a computation is recorded with
    ///   that exit, `return` when the bridge is the inserted one and `become`
    ///   otherwise; a `return` crossing a handler's frame is minted as the
    ///   capture [`Exits::unwind`](exits::unwind) writes, and that capture
    ///   recorded as the exit; a `break`'s returner is recorded as a break; a
    ///   loop end written without an exit is bound and its loop run again, as
    ///   [`ExitsRef::rerun`] writes it; a constructor awaiting its data
    ///   family's application, or the constructor a field it stands in belongs
    ///   to, is left for that node, which mints it first; a node with no plan,
    ///   or whose plan was carried out, or under a refused declaration outside
    ///   a payload and outside the types a module signature states, is left as
    ///   it is.
    /// - provides: the per-position half of
    ///   [`Self::mint`](crate::lower::Expressions::mint).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration leaves its ordinary plans
    ///   untouched but still permits its attribute payloads to mint;
    ///   carried-out plans are not minted twice when a manifest and the full
    ///   traversal both reach them; a tail of each polarity records its own
    ///   exit once; a call of no arguments answers at the call, its head at the
    ///   head.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_signature_s_types_answer_whatever_its_members_1115`
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_of_no_arguments_is_the_call_the_source_wrote_364`
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(
        captures: before = (
            (self.cx().collected.refused(position).0
                && !self.shared().in_payload(position).0
                && !self.shared().stated_apart(position).0)
                || self.cx().awaiting.contains(&position),
            matches!(
                self.cx().plans.get(position),
                None | Some(&Plan::Unplanned)
            ) || self.cx().taken.get(position) == Some(&true),
            self.cx().lowered_at(position),
            self.cx().plans.count(),
            usize::from(self.cx().lowered.count()),
        ),
        ensures: self.cx().plans.count() == before.3
            && usize::from(self.cx().lowered.count()) == before.4
            && (if before.0 || before.1 {
                self.cx().lowered_at(position) == before.2
            }
            else {
                self.cx().taken.get(position) == Some(&true)
            }),
    )]
    fn mint_at(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        if self.cx().collected.refused(position).0
            && !self.shared().in_payload(position).0
            && !self.shared().stated_apart(position).0
        {
            return;
        }
        // A constructor classified by its place in a data family's application
        // or in a call waits for the application or the call, and one
        // classified by a field for the constructor the field belongs to: each
        // mints it once everything before it is minted.
        if self.cx().awaiting.contains(&position) {
            return;
        }
        self.mint_released(position, sink);
    }

    /// Mint the node at `position` after each constructor waiting on it.
    ///
    /// # Specification
    /// - requires: as [`Self::mint_planned`], but for the constructors that
    ///   wait on the node.
    /// - ensures: each argument of a data family's application or a call and
    ///   each field of a constructor that waits on it minted first, left to
    ///   right, each after the constructors waiting on it in turn; then the
    ///   node, as [`Self::mint_planned`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the order is the claim, and the minted nodes keep
    ///   no record of it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor written as a family's argument, one
    ///   written as a call's argument, and one written in a field typed by its
    ///   family's parameter, each minted before the node it waits on.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
    fn mint_released(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        // A node something waits on is visited twice: first to queue the
        // constructors waiting on it, leftmost on top, then, once those are
        // minted, to mint it. A node nothing waits on, nearly every node, is
        // minted at once, and the queue allocates only when something waits.
        let mut work: Vec<(NodeIndex, bool)> = Vec::new();
        let mut next = Some((position, false));
        while let Some((at, released)) = next {
            let waiting = match self.cx().plans.get(at) {
                Some(&(Plan::Data(_, arguments) | Plan::Application(_, arguments)))
                    if !released =>
                {
                    Some(arguments)
                },
                Some(&(Plan::Constructor(constructed) | Plan::Ports(constructed, _)))
                    if !released =>
                {
                    Some(constructed.fields)
                },
                Some(_) | None => None,
            };
            let waited = waiting.is_some_and(|waiting| {
                self.cx()
                    .operands
                    .read(waiting)
                    .iter()
                    .any(|operand| self.cx().awaiting.contains(operand))
            });
            if let (true, Some(waiting)) = (waited, waiting) {
                work.push((at, true));
                let first = work.len();
                let waiting = self.shared().spread(waiting);
                for place in waiting.start .. waiting.end {
                    if let Some(&operand) = self.cx().operands.entries().get(place)
                        && self.cx_mut().awaiting.remove(&operand)
                    {
                        work.push((operand, false));
                    }
                }
                if let Some(queued) = work.get_mut(first ..) {
                    queued.reverse();
                }
            }
            else {
                self.mint_planned(at, sink);
            }
            next = work.pop();
        }
    }

    /// Mint the node at `position` by its plan, once, whatever declaration or
    /// application it waits on: [`Self::mint_at`]'s mint itself.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan is carried out once, as [`Self::mint_at`] states,
    ///   and kept; a type a term quotes is carried from its telescope into the
    ///   term's context before the quote wraps it, while a value a type reads
    ///   stays in the type's telescope; a member's name standing for a value
    ///   type is recorded as its stand-in, and one standing for a computation
    ///   type labelled with it; the value type a top-level member's own
    ///   definition mints is recorded under the member's name; a node with no
    ///   plan, or whose plan was carried out, is left as it is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor awaiting its family's application is
    ///   minted at its slot's type once the application reaches it, and a type
    ///   quoted in a body past an unmentioned parameter reads its binders at
    ///   their indices in the body; a grouped type head stands for what it
    ///   groups.
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `gandr-surface-lowering::lower::tests::a_quote_in_a_body_reads_past_an_unmentioned_parameter`
    /// - witness: `gandr-surface-lowering::lower::tests::a_type_head_answers_at_what_it_stands_for`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
    #[spec(
        captures: before = (
            matches!(
                self.cx().plans.get(position),
                None | Some(&Plan::Unplanned)
            ) || self.cx().taken.get(position) == Some(&true),
            self.cx().lowered_at(position),
            self.cx().plans.count(),
            usize::from(self.cx().lowered.count()),
        ),
        ensures: self.cx().plans.count() == before.2
            && usize::from(self.cx().lowered.count()) == before.3
            && (if before.0 {
                self.cx().lowered_at(position) == before.1
            }
            else {
                self.cx().taken.get(position) == Some(&true)
            }),
    )]
    fn mint_planned(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        let Some(taken) = self.cx_mut().taken.get_mut(position)
        else {
            return;
        };
        if core::mem::replace(taken, true) {
            return;
        }
        let Some(plan) = self.cx().plans.get(position)
        else {
            return;
        };
        if *plan == Plan::Unplanned {
            return;
        }
        let Maybe::Present(origin) = self.cx().origin_at(position)
        else {
            return;
        };
        // A call through a joint has the joint's variable at its head. The
        // source writes the member's name there and never the joint, so the
        // variable and its force are the joint's, located at the name (#5519).
        let joint = self.cx().injected.contains_key(&position);
        let origin = if joint {
            origin.inserted(Insertion::Joint)
        }
        else {
            origin
        };
        let bridge = self
            .cx()
            .bridges
            .get(position)
            .copied()
            .unwrap_or(Bridge::Bare);
        let stands_in = matches!(*plan, Plan::Transparent(_) | Plan::Instantiated(..))
            && self.cx().stand_ins.contains(&position);
        let minted = self.shared().mint_plan(plan, sink, origin);
        if stands_in && let Maybe::Present(Lowered::ValueType(id)) = minted {
            sink.origins.record_stand_in(id, origin);
        }
        // A definition that names another member stands in for that member's
        // type, which keeps its own name.
        if !stands_in
            && let Maybe::Present(Lowered::ValueType(id)) = minted
            && let Some(&named) = self.cx().defining.get(&position)
            && let Maybe::Present(name) = self.cx().origin_at(named)
        {
            sink.origins.record_member(id, name);
        }
        // A member's computation type is closed, so it reads under no binder.
        if stands_in && let Maybe::Present(Lowered::CompType(ty)) = minted {
            sink.origins.record_label(Label {
                span: origin.span(),
                labelled: Labelled::CompType {
                    ty,
                    context: Vec::new(),
                },
            });
        }
        if let Plan::Scope(ref scoped) = *plan
            && let Maybe::Present(Lowered::Computation(scope)) = minted
            && let Some((owner, laws)) = capability::scope_laws(scoped, scope, sink, origin)
        {
            self.cx_mut()
                .handler_laws
                .entry(owner)
                .or_default()
                .extend(laws);
        }
        let cx = self.cx_mut();
        if let Maybe::Present(Lowered::Value(head)) = minted
            && let Some(&(caller, ref planned)) = cx.planned_supplies.get(&position)
        {
            cx.supplies
                .entry(caller)
                .or_default()
                .extend(
                    planned
                        .iter()
                        .map(|&(binder, stage)| gandr_core_term::staged::Supply {
                            head,
                            binder,
                            stage,
                        }),
                );
        }
        if let Maybe::Present(_) = minted
            && let Some(planned) = self.cx_mut().planned_models.remove(&position)
        {
            for slot in planned {
                Models::new(self.host()).mint_model(slot, sink, origin);
            }
        }
        // A type a term quotes was minted in its telescope, which counts a
        // typed binder only once a type names it; the term's context binds
        // every binder, so the quote is carried into it (#540). A body's quote
        // counts in its own telescope, which its reads extend without making
        // the signature's arrows dependent (#547). A value a type reads stays
        // in that type's telescope.
        let minted = match (bridge, minted) {
            (Bridge::Inserted(Insertion::Quote), Maybe::Present(Lowered::ValueType(quoted)))
                if !self.cx().type_read.contains(&position)
                    && !self.cx().in_type.contains(&position) =>
            {
                let frame = self.cx().reading(position).frame();
                Maybe::Present(Lowered::ValueType(
                    NativeRef::over(self.cx()).relocate_value_type(
                        quoted,
                        frame,
                        Telescope::Quote,
                        sink,
                        origin,
                    ),
                ))
            },
            (Bridge::Inserted(Insertion::Quote), Maybe::Present(Lowered::CompType(quoted)))
                if !self.cx().type_read.contains(&position)
                    && !self.cx().in_type.contains(&position) =>
            {
                let frame = self.cx().reading(position).frame();
                Maybe::Present(Lowered::CompType(
                    NativeRef::over(self.cx()).relocate_comp_type(
                        quoted,
                        frame,
                        Telescope::Quote,
                        sink,
                        origin,
                    ),
                ))
            },
            (_, minted) => minted,
        };
        // A call standing as the record of its outputs binds each and returns
        // the record, labelled when every output is named.
        let minted = match (bridge, minted, self.cx().packed.get(&position)) {
            (
                Bridge::Inserted(Insertion::Nested | Insertion::Bound | Insertion::Endpoint),
                Maybe::Present(Lowered::Computation(call)),
                Some(labels),
            ) => arity::mint_record_of_outputs(call, labels, sink, origin),
            (_, minted, _) => minted,
        };
        // A call of no arguments is its head's force, so that force is the
        // call the source wrote: it answers at the call, not at the head.
        let called = self
            .cx()
            .nullary
            .get(&position)
            .map(|&call| self.cx().origin_at(call));
        let bridged = match (bridge, minted, called) {
            (
                Bridge::Inserted(Insertion::Force),
                Maybe::Present(Lowered::Value(forced)),
                Some(Maybe::Present(call)),
            ) => {
                let id = sink.arena.computation_force(forced);
                Maybe::Present(sink.computation(id, call))
            },
            (Bridge::Inserted(Insertion::Force), Maybe::Present(Lowered::Value(forced)), _)
                if joint =>
            {
                let id = sink.arena.computation_force(forced);
                Maybe::Present(sink.computation(id, origin))
            },
            (_, minted, _) => sink.bridge(minted, bridge, origin),
        };
        // A tail's annotation `(e : T)` returns `e` ascribed `-F T`, as the
        // written `return (e : T)` does.
        let bridged = match (bridge, bridged, self.cx().ascribed.get(&position)) {
            (
                Bridge::Inserted(Insertion::Return),
                Maybe::Present(Lowered::Computation(returned)),
                Some(&classifier),
            ) => {
                let inserted = origin.inserted(Insertion::Return);
                self.shared()
                    .ascribed_return(returned, position, classifier, sink, inserted)
                    .map(|ascribed| sink.computation(ascribed, inserted))
            },
            (_, bridged, _) => bridged,
        };
        let bridged = match bridged {
            Maybe::Present(Lowered::Computation(returned))
                if self.cx().crossing.contains(&position) =>
            {
                Maybe::Present(Lowered::Computation(exits::unwind(sink, returned, origin)))
            },
            bridged @ (Maybe::Present(_) | Maybe::Absent(_)) => bridged,
        };
        if self.cx().leaving.contains(&position)
            && let Maybe::Present(Lowered::Computation(exit)) = bridged
        {
            let _first = sink.exits.insert(exit);
            if self.cx().inferred.contains(&position) {
                self.cx_mut().elided.push((position, match bridge {
                    Bridge::Inserted(Insertion::Return) => Exit::Return,
                    Bridge::Bare | Bridge::Inserted(_) | Bridge::HeadCall => Exit::Become,
                }));
            }
            else if let Some((operand, returned)) =
                ExitsRef::new(self.host_ref()).elidable_at(position)
            {
                self.cx_mut().elidable.push((position, operand, returned));
            }
        }
        if self.cx().breaking.contains(&position)
            && let Maybe::Present(Lowered::Computation(broken)) = bridged
        {
            let _first = sink.breaks.insert(broken);
        }
        let bridged = match (self.cx().reentered.get(&position), bridged) {
            (Some(&own), Maybe::Present(Lowered::Computation(end))) => {
                Maybe::Present(Lowered::Computation(
                    ExitsRef::new(self.host_ref()).rerun(position, end, own, sink, origin),
                ))
            },
            (_, bridged) => bridged,
        };
        let bridged = match bridged {
            Maybe::Present(Lowered::Computation(end)) if self.cx().trailing.contains(&position) => {
                Maybe::Present(Lowered::Computation(
                    ExitsRef::new(self.host_ref()).conclude(position, end, sink, origin),
                ))
            },
            bridged @ (Maybe::Present(_) | Maybe::Absent(_)) => bridged,
        };
        if let Some(held) = self.cx_mut().lowered.get_mut(position) {
            *held = bridged;
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Carry out one plan.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan's core node, minted over its children's lowered
    ///   nodes with its origin recorded; an adopted child's own node for a
    ///   transparent plan; nothing when a child did not lower at the sort the
    ///   plan takes. A variable is minted in its binder's zone: the linear zone
    ///   for a fork's end, the intuitionistic zone for every other binder; a
    ///   decode's code carries the written origin and its type the inserted
    ///   one; a functor parameter's abstract type is labelled at the kind its
    ///   component reads ([`Self::parameter_kind`]).
    /// - provides: the per-node half of
    ///   [`Self::mint`](crate::lower::Expressions::mint).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the admitted plan families lower to their matching
    ///   core families; grouping reuses its child result and an unplanned node
    ///   cannot manufacture a value. Concrete constructors and origins are
    ///   witnessed through complete declarations and the fragment-specific
    ///   examples.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_parameter_s_abstract_type_answers_at_its_kind_2183`
    #[spec(
        captures: promised = (
            match *plan {
                | Plan::Expansion(family, _) if self.cx().family_produced(family) == Produced::CompType => {
                    Some(Produced::CompType)
                },
                | Plan::Instantiated(_, defined) if self.cx().computation_members.contains(&defined) => {
                    Some(Produced::CompType)
                },
                | Plan::Variable(..)
                | Plan::ValueHole(_)
                | Plan::Constant(_)
                | Plan::Primitive(_)
                | Plan::Boolean(_)
                | Plan::Literal(_)
                | Plan::Natural(..)
                | Plan::StaticApplication(..)
                | Plan::Tuple(_)
                | Plan::List(_)
                | Plan::Record(_)
                | Plan::RecordUpdate(..)
                | Plan::Injection(..)
                | Plan::StaticLambda(_)
                | Plan::Thunk(_)
                | Plan::Here(_)
                | Plan::Funext(..)
                | Plan::Equiv(..)
                | Plan::Univalence(_)
                | Plan::PathProduct(..)
                | Plan::Ua { .. }
                | Plan::Fill { .. }
                | Plan::ListNil
                | Plan::ListCons(..)
                | Plan::Run(_)
                | Plan::SessionRelated(..)
                | Plan::Stay(_)
                | Plan::Forward(_)
                | Plan::FunctionFlow(..)
                | Plan::FlowProduct(..)
                | Plan::Recorded(_)
                | Plan::Dialogue(_)
                | Plan::Constructor(_)
                | Plan::Ports(..)
                | Plan::Ascribed(..)
                | Plan::Packed(_) => Some(Produced::Value),
                | Plan::Plugged { .. }
                | Plan::CompHole(_) | Plan::PrimitiveCall(..) | Plan::Interpolated(..) | Plan::Return(_) | Plan::ReturnAll(_) | Plan::SelectedOutput { .. } | Plan::Force(_) | Plan::Lambda(..) | Plan::Block(_) | Plan::Loop(_) | Plan::While(..) | Plan::If(_) | Plan::For(..) | Plan::Break | Plan::Reenter(_) | Plan::Application(..) | Plan::Called(..) | Plan::Forced(_) | Plan::Case(_) | Plan::EmptyCase(_) | Plan::Copattern(_) | Plan::Observe(..) | Plan::Select(..) | Plan::Field(..) | Plan::SubRecord(..) | Plan::Projected(_) | Plan::Derived(_) | Plan::Transport(..) | Plan::TelescopeTransport(_) | Plan::Exercise(_) | Plan::Method(_) | Plan::Scope(_) | Plan::Resume(..) | Plan::Abandon(_) | Plan::Action(..) | Plan::Access(_) | Plan::Ride(..) | Plan::Decompose(_) | Plan::FlowThen(..) | Plan::World(world::Worlded::Hold { .. } | world::Worlded::Migrate { .. }) => {
                    Some(Produced::Computation)
                },
                | Plan::Atom(_)
                | Plan::Sealed(_)
                | Plan::Instantiated(..)
                | Plan::Universe(_)
                | Plan::ValueFunction(..)
                | Plan::Telescope(..)
                | Plan::StaticPi(..)
                | Plan::Product(..)
                | Plan::RecordType(..)
                | Plan::Sum(..)
                | Plan::Former(
                    TypeFormer::Thunk
                    | TypeFormer::List
                    | TypeFormer::Run
                    | TypeFormer::Prefix
                    | TypeFormer::Dialogue,
                    _,
                )
                | Plan::Path(..)
                | Plan::Flow(..)
                | Plan::Relation(..)
                | Plan::Bundle(_)
                | Plan::Stack(..)
                | Plan::Data(..)
                | Plan::Expansion(..)
                | Plan::Capability(..)
                | Plan::Session(..)
                | Plan::World(world::Worlded::At { .. })
                | Plan::Staged(..)
                | Plan::Patched { .. }
                | Plan::Kept(..)
                | Plan::Carrier(..)
                | Plan::FixedCarrier(..)
                | Plan::LinearArrow(_, _, crate::form::Boxed(true)) => Some(Produced::ValueType),
                | Plan::Arrow(..) | Plan::DependentArrow(..) | Plan::LinearArrow(_, _, crate::form::Boxed(false)) | Plan::Returns(_) | Plan::With(..) | Plan::Codata(..) | Plan::Former(TypeFormer::Returner, _) | Plan::Effectful(..) => {
                    Some(Produced::CompType)
                },
                | Plan::Decode(_, _, universe) | Plan::Unquote(_, _, universe) | Plan::Reapplied(_, _, _, universe) => Some(match universe.sort {
                    | GroundSort::Value => Produced::ValueType,
                    | GroundSort::Computation => Produced::CompType,
                }),
                | Plan::Unplanned | Plan::Generic | Plan::Transparent(_) | Plan::Function(_) => None,
            },
            match *plan {
                | Plan::Transparent(child) => Some(self.cx().lowered_at(child)),
                | _ => None,
            },
            matches!(plan, Plan::Unplanned | Plan::Generic),
            matches!(plan, Plan::Function(_)),
        ),
        ensures: |ret| {
            promised.1.map_or_else(
                || {
                    if promised.2 {
                        ret == Maybe::Absent(lowered::Absent::Unminted)
                    }
                    else if promised.3 {
                        matches!(
                            ret,
                            Maybe::Absent(_) | Maybe::Present(Lowered::Function { .. })
                        )
                    }
                    else {
                        matches!(
                            (promised.0, ret),
                            (Some(_), Maybe::Absent(_))
                                | (Some(Produced::Value), Maybe::Present(Lowered::Value(_)))
                                | (
                                    Some(Produced::Computation),
                                    Maybe::Present(Lowered::Computation(_))
                                )
                                | (
                                    Some(Produced::ValueType),
                                    Maybe::Present(Lowered::ValueType(_))
                                )
                                | (
                                    Some(Produced::CompType),
                                    Maybe::Present(Lowered::CompType(_))
                                )
                        )
                    }
                },
                |child| ret == child,
            )
        },
    )]
    fn mint_plan(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            Plan::ValueHole(hole) => {
                let id = sink.arena.value_hole(hole);
                if self.cx().nominations.get(&hole) == Some(&implicit::Nomination::Wildcard) {
                    sink.origins.record_omitted(id, Omitted::Wildcard);
                }
                Maybe::Present(sink.value(id, origin))
            },
            Plan::CompHole(hole) => {
                let id = sink.arena.computation_hole(hole);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Primitive(primitive) => {
                let id = primitive.thunk(sink.arena);
                if let Some(&Value::Primitive { body, .. }) = sink.arena.value(id) {
                    let mut current = body;
                    let mut ancestors = [body; 3];
                    let mut count = 0_usize;
                    for ancestor in &mut ancestors {
                        *ancestor = current;
                        count = count.saturating_add(1);
                        match sink.arena.computation(current) {
                            Some(&Computation::Lambda(inner)) => current = inner,
                            Some(&Computation::Primitive { ref arguments, .. }) => {
                                for &argument in arguments.iter().rev() {
                                    sink.origins.record_value(argument, origin);
                                }
                                break;
                            },
                            _ => break,
                        }
                    }
                    for &computation in ancestors.iter().take(count).rev() {
                        sink.origins.record_computation(computation, origin);
                    }
                }
                Maybe::Present(sink.value(id, origin))
            },
            Plan::PrimitiveCall(primitive, arguments) => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    Arguments::Unary(argument) => {
                        self.cx().value_at(argument).map(Arguments::Unary)
                    },
                    Arguments::Binary([first, second]) => {
                        self.cx().value_at(first).and_then(|first| {
                            self.cx()
                                .value_at(second)
                                .map(|second| Arguments::Binary([first, second]))
                        })
                    },
                };
                arguments.map(|arguments| {
                    let id = sink.arena.computation_primitive(primitive, arguments);
                    sink.computation(id, origin)
                })
            },
            Plan::Interpolated(append, segments) => {
                self.mint_interpolated(append, segments, sink, origin)
            },
            Plan::Unplanned | Plan::Generic => Maybe::Absent(lowered::Absent::Unminted),
            Plan::Variable(index, binder) => {
                let id = sink
                    .arena
                    .value_variable(self.cx().scope.zone(binder), index);
                // The joint's variable at the head of a call through the joint
                // uses no binder that the source writes (#5519).
                if origin.provenance() != Provenance::Inserted(Insertion::Joint)
                    && let Maybe::Present(site) = self.cx().scope.site(binder)
                {
                    sink.origins.record_binding(id, site);
                }
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Constant(constant) => {
                let id = sink.arena.value_constant(constant);
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Boolean(side) => {
                let unit = sink.arena.value_unit();
                sink.origins.record_value(unit, origin);
                let id = sink.arena.value_injection(side.into(), unit);
                sink.origins.record_value(id, origin);
                // The literal synthesises `Bool`, as a number synthesises its
                // carrier, so a model implicit it argues is resolved there
                // (#3350).
                let Lowered::ValueType(boolean) =
                    sink.atom(TypeAtom::Boolean, origin.inserted(Insertion::Classifier))
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let ascribed = sink.arena.value_ascribe(id, boolean);
                Maybe::Present(sink.value(ascribed, origin))
            },
            Plan::Literal(ref literal) => {
                let id = sink.arena.value_literal(literal.clone());
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Natural(naturals, ref magnitude) => {
                Maybe::Present(natural::mint_natural(naturals, magnitude, sink, origin))
            },
            Plan::Atom(atom) => Maybe::Present(sink.atom(atom, origin)),
            Plan::Instantiated(instance, defined) => {
                match self.cx().instance_types.get(&(instance, defined)) {
                    Some(&InstanceType::Computation(id)) => Maybe::Present(Lowered::CompType(id)),
                    Some(&InstanceType::Value(id)) => Maybe::Present(Lowered::ValueType(id)),
                    None => Maybe::Absent(lowered::Absent::Unminted),
                }
            },
            Plan::Sealed(atom) => {
                let id = sink.arena.value_type_abstract(atom);
                sink.origins.record_value_type(id, origin);
                // A functor parameter's abstract type is formed only where an
                // application checks the functor: it answers at its kind.
                if let Some(kind) = self.parameter_kind(atom, sink) {
                    sink.origins.record_label(Label {
                        span: origin.span(),
                        labelled: Labelled::Kind(kind),
                    });
                }
                Maybe::Present(Lowered::ValueType(id))
            },
            Plan::Universe(universe) => {
                let id = sink.arena.value_type_universe(
                    Sort::Ground(universe.sort),
                    Level::constant(universe.level),
                );
                sink.origins.record_value_type(id, origin);
                Maybe::Present(Lowered::ValueType(id))
            },
            Plan::Decode(code, arguments, universe) => {
                self.mint_decode(code, arguments, universe, sink, origin)
            },
            Plan::Unquote(code, arguments, universe) => {
                let head = self.written_head(origin);
                self.mint_unquote(code, arguments, universe, sink, (origin, head))
            },
            Plan::Reapplied(code, arguments, again, universe) => {
                let head = self.written_head(origin);
                self.mint_reapplied(code, (arguments, again), universe, sink, (origin, head))
            },
            Plan::Carrier(code, selected, ref label) => ModelsRef::new(self.host_ref())
                .mint_carrier(code, selected, label.as_ref(), sink, origin),
            Plan::FixedCarrier(code, written) => {
                ModelsRef::new(self.host_ref()).mint_fixed_carrier(code, written, sink, origin)
            },
            Plan::Called(code, arguments) => {
                let head = self.written_head(origin);
                self.mint_called(code, arguments, sink, (origin, head))
                    .map(Lowered::Computation)
            },
            Plan::Forced(code) => {
                let head = self.written_head(origin);
                Maybe::Present(Lowered::Computation(self.mint_forced(
                    code,
                    sink,
                    (origin, head),
                )))
            },
            Plan::StaticApplication(code, arguments) => self
                .mint_code(code, arguments, sink, origin)
                .map(Lowered::Value),
            Plan::Tuple(members) => self.mint_tuple(members, sink, origin),
            Plan::ReturnAll(members) => self.mint_return_all(members, sink, origin),
            Plan::SelectedOutput { call, arity, index } => ModelsRef::new(self.host_ref())
                .mint_selected_output((call, arity, arity::Place(index)), sink, origin),
            Plan::Plugged { left, right, arity } => {
                ModelsRef::new(self.host_ref()).mint_plugged((left, right, arity), sink, origin)
            },
            Plan::List(elements) => self.mint_list(elements, sink, origin),
            Plan::Record(ref fields) => {
                ModelsRef::new(self.host_ref()).mint_record(fields, sink, origin)
            },
            Plan::RecordUpdate(base, ref fields) => {
                ModelsRef::new(self.host_ref()).mint_record_update(base, fields, sink, origin)
            },
            Plan::Injection(summand, body) => {
                ModelsRef::new(self.host_ref()).mint_injection(summand, body, sink, origin)
            },
            Plan::ValueFunction(domains, codomain) => {
                self.mint_value_function(domains, codomain, sink, origin)
            },
            Plan::Telescope(entries, codomain) => {
                ModelsRef::new(self.host_ref()).mint_telescope(entries, codomain, sink, origin)
            },
            Plan::DependentArrow(entries, codomain) => ModelsRef::new(self.host_ref())
                .mint_dependent_arrow(entries, codomain, sink, origin),
            Plan::LinearArrow(entries, codomain, boxed) => ModelsRef::new(self.host_ref())
                .mint_linear_arrow(entries, codomain, boxed, sink, origin),
            Plan::Returns(entries) => ModelsRef::new(self.host_ref()).mint_returns(
                entries,
                gandr_core_term::effect::EffectRow::EMPTY,
                sink,
                origin,
            ),
            Plan::Transparent(child) => self.cx().lowered_at(child),
            Plan::Former(former, argument) => self.mint_former(former, argument, sink, origin),
            Plan::Application(head, arguments) => {
                self.mint_application(head, arguments, sink, origin)
            },
            Plan::Function(function) => self.mint_function(&function, sink, origin),
            Plan::Method(called) => {
                CapabilityRef::new(self.host_ref()).mint_method(called, sink, origin)
            },
            Plan::Data(constant, arguments) => {
                NativeRef::over(self.cx()).mint_family(constant, arguments, sink, origin)
            },
            Plan::Codata(constant, arguments) => {
                NativeRef::over(self.cx()).mint_codata(constant, arguments, sink, origin)
            },
            Plan::Expansion(family, arguments) => {
                let expanded =
                    ModelsRef::new(self.host_ref()).mint_expansion(family, arguments, sink, origin);
                let context = |lowerer: &Self, frame| -> Vec<String> {
                    lowerer
                        .cx()
                        .scope
                        .telescope_names(frame, lowerer.telescope_at(origin.node()))
                        .into_iter()
                        .map(|name| String::from(name.as_ref()))
                        .collect()
                };
                if let Some(&(span, frame)) = self.cx().expansions.get(&origin.node()) {
                    let labelled = match expanded {
                        Maybe::Present(Lowered::ValueType(ty)) => Some(Labelled::ValueType {
                            ty,
                            context: context(self, frame),
                        }),
                        Maybe::Present(Lowered::CompType(ty)) => Some(Labelled::CompType {
                            ty,
                            context: context(self, frame),
                        }),
                        Maybe::Present(_) | Maybe::Absent(_) => None,
                    };
                    if let Some(labelled) = labelled {
                        sink.origins.record_label(Label { span, labelled });
                    }
                }
                expanded
            },
            Plan::Constructor(constructed) => {
                NativeRef::over(self.cx()).mint_constructor(constructed, sink, origin)
            },
            Plan::Ports(constructed, ref ports) => {
                NativeRef::over(self.cx()).mint_ports(constructed, ports, sink, origin)
            },
            Plan::Case(case) => NativeRef::over(self.cx()).mint_case(case, sink, origin),
            Plan::EmptyCase(scrutinee) => self.cx().value_at(scrutinee).map(|scrutinised| {
                let id = sink.arena.computation_case(scrutinised, &[]);
                sink.computation(id, origin)
            }),
            Plan::Product(components) => self.mint_product(components, sink, origin),
            Plan::RecordType(ref fields, binders, last, labelled) => ModelsRef::new(
                self.host_ref(),
            )
            .mint_labelled_type(fields, binders, (last, labelled), sink, origin),
            Plan::Sum(summands, labels) => {
                ModelsRef::new(self.host_ref()).mint_sum(summands, labels, sink, origin)
            },
            Plan::With(entries, labels) => {
                ModelsRef::new(self.host_ref()).mint_with(entries, labels, sink, origin)
            },
            Plan::Copattern(clauses) => {
                ModelsRef::new(self.host_ref()).mint_copattern(clauses, sink, origin)
            },
            Plan::Observe(subject, observed, thunked) => ModelsRef::new(self.host_ref())
                .mint_observe(subject, observed, thunked, sink, origin),
            Plan::Select(subject, selected, ref labelled) => ModelsRef::new(self.host_ref())
                .mint_select(subject, selected, labelled.as_ref(), sink, origin),
            Plan::Field(subject, ref label) => self.cx().value_at(subject).map(|held| {
                let id = sink
                    .arena
                    .computation_record_projection(held, label.clone());
                sink.origins.record_computation(id, origin);
                Lowered::Computation(id)
            }),
            Plan::SubRecord(subject, ref selected) => {
                ModelsRef::new(self.host_ref()).mint_sub_record(subject, selected, sink, origin)
            },
            Plan::Projected(projected) => {
                NativeRef::over(self.cx()).mint_projected(projected, sink, origin)
            },
            Plan::Block(block) => self.mint_block(block, sink).map(Lowered::Computation),
            Plan::Loop(body) => ExitsRef::new(self.host_ref()).mint_loop(body, sink, origin),
            Plan::While(condition, body) => {
                ExitsRef::new(self.host_ref()).mint_while(condition, body, sink, origin)
            },
            Plan::If(conditional) => self.mint_conditional(conditional, sink, origin),
            Plan::For(list, body) => {
                ExitsRef::new(self.host_ref()).mint_for(list, body, sink, origin)
            },
            Plan::Break => {
                let unit = sink.arena.value_unit();
                sink.origins.record_value(unit, origin);
                let id = sink.arena.computation_return(unit);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Reenter(reentry) => {
                let id = loops::again(reentry, sink, origin);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Derived(derived) => {
                IdentitiesRef::new(self.host_ref()).mint_derived(derived, sink, origin)
            },
            Plan::TelescopeTransport(transported) => IdentitiesRef::new(self.host_ref())
                .mint_telescope_transport(transported, sink, origin),
            Plan::Capability(ref authority, grade, region) => {
                capability::mint_capability(authority, grade, region, sink, origin)
            },
            Plan::Effectful(ref row, argument) => {
                CapabilityRef::new(self.host_ref()).mint_effectful(row, argument, sink, origin)
            },
            Plan::Exercise(ref exercised) => {
                CapabilityRef::new(self.host_ref()).mint_exercise(exercised, sink, origin)
            },
            Plan::Scope(ref scoped) => {
                CapabilityRef::new(self.host_ref()).mint_scope(scoped, sink, origin)
            },
            Plan::Resume(continuation, reply) => {
                CapabilityRef::new(self.host_ref()).mint_resume(continuation, reply, sink, origin)
            },
            Plan::Abandon(continuation) => {
                CapabilityRef::new(self.host_ref()).mint_abandon(continuation, sink, origin)
            },
            Plan::Session(ref protocol, payloads, ref written) => {
                CapabilityRef::new(self.host_ref())
                    .mint_session(protocol, payloads, written, sink, origin)
            },
            Plan::Action(ref action, subject, ref arms) => CapabilityRef::new(self.host_ref())
                .mint_action(action, (subject, arms), sink, origin),
            Plan::Access(accessed) => {
                CapabilityRef::new(self.host_ref()).mint_access(accessed, sink, origin)
            },
            Plan::World(worlded) => self.mint_world(worlded, sink, origin),
            Plan::Staged(base, stage) => self.mint_staged(base, stage, sink, origin),
            Plan::Patched {
                ref fields,
                ref fixed,
                ref meets,
                member,
            } => self.mint_patched_type(fields, (fixed, meets), member, sink, origin),
            Plan::Kept(inner, region) => self.cx().value_type_at(inner).map(|inner| {
                let id = sink.arena.value_type_kept(inner, region);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            Plan::Recorded(ref moves) => {
                IdentitiesRef::new(self.host_ref()).mint_recorded(moves, sink, origin)
            },
            Plan::Dialogue(ref moves) => {
                IdentitiesRef::new(self.host_ref()).mint_dialogue(moves, sink, origin)
            },
            Plan::Decompose(dialogue) => {
                IdentitiesRef::new(self.host_ref()).mint_decompose(dialogue, sink, origin)
            },
            Plan::Ride(motive, flow, value) => {
                IdentitiesRef::new(self.host_ref()).mint_ride((motive, flow, value), sink, origin)
            },
            Plan::FlowThen(first, second) => {
                IdentitiesRef::new(self.host_ref()).mint_flow_then(first, second, sink, origin)
            },
            Plan::Relation(relation, left, right) => IdentitiesRef::new(self.host_ref())
                .mint_relation(relation, [left, right], sink, origin),
            Plan::Bundle(ref signature) => {
                ModelsRef::new(self.host_ref()).mint_model_type(signature, sink, origin)
            },
            Plan::Packed(ref packed) => {
                ModelsRef::new(self.host_ref()).mint_packed(packed, sink, origin)
            },
            Plan::Arrow(..)
            | Plan::StaticPi(..)
            | Plan::Path(..)
            | Plan::Flow(..)
            | Plan::Stack(..)
            | Plan::SessionRelated(..)
            | Plan::Stay(_)
            | Plan::Forward(_)
            | Plan::FunctionFlow(..)
            | Plan::FlowProduct(..)
            | Plan::StaticLambda(_)
            | Plan::Thunk(_)
            | Plan::Here(_)
            | Plan::Funext(..)
            | Plan::Equiv(..)
            | Plan::Univalence(_)
            | Plan::PathProduct(..)
            | Plan::Ua { .. }
            | Plan::Fill { .. }
            | Plan::ListNil
            | Plan::ListCons(..)
            | Plan::Transport(..)
            | Plan::Return(_)
            | Plan::Ascribed(..)
            | Plan::Force(_)
            | Plan::Run(_)
            | Plan::Lambda(..) => self.mint_over(plan, sink, origin),
        }
    }

    /// Mint a code: its head, applied statically to the arguments `arguments`
    /// names in the operand store, left to right.
    ///
    /// # Specification
    /// - requires: every type position has been classified, so every binder a
    ///   code names is recorded as mentioned; every argument is already minted
    ///   or absent.
    /// - ensures: a binder's head is the variable at its telescope index from
    ///   the use site and a declaration's the constant; `h(v1, …, vn)` mints as
    ///   `sapp(… sapp(h, v1) …, vn)`, every node with the written origin;
    ///   nothing is minted when an argument did not lower.
    /// - provides: the head of a decode and the value of a static application.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `arguments`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare binder, a bare declaration, and an operator
    ///   applied to one and to three arguments, each asserted as the exact core
    ///   node read back out of the arena.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(id) => match sink.arena.value(id) {
                | Some(&gandr_core_term::Value::StaticApplication(..)) => {
                    arguments != FormStretch::default()
                },
                | Some(
                    &(gandr_core_term::Value::Variable { .. }
                    | gandr_core_term::Value::Constant(_)),
                ) => arguments == FormStretch::default(),
                | _ => false,
            },
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — bound and constant codes are applied to their
    ///   arguments in source order; every node in the static application spine
    ///   records the written origin, rather than an inserted decode origin, the
    ///   operator of a call the head it is written at; a type family's
    ///   parameter named alone is labelled at its written kind.
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::tests::modules::a_family_s_parameter_under_a_data_type_answers_at_its_kind_3142`
    #[spec(
        ensures: |ret| match self.first_absent(arguments, |argument| self.cx().value_at(argument)) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => {
                matches!(ret, Maybe::Present(id) if sink.origins.value(id) == Maybe::Present(origin))
            },
        },
    )]
    #[inline]
    pub fn mint_code(
        &self,
        code: Code,
        arguments: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        if let Some(reason) = self.first_absent(arguments, |argument| self.cx().value_at(argument))
        {
            return Maybe::Absent(reason);
        }
        let written = self.cx().operands.read(arguments);
        let mut applied = match code {
            Code::Bound {
                from,
                binder,
                telescope,
            } => {
                // A family's body is never checked where it is written, so a
                // parameter it names alone answers at its kind.
                if written.is_empty()
                    && let Some(kind) =
                        ModelsRef::new(self.host_ref()).family_parameter_kind(binder)
                {
                    sink.origins.record_label(Label {
                        span: origin.span(),
                        labelled: Labelled::Kind(kind),
                    });
                }
                sink.arena.value_variable(
                    Zone::Intuitionistic,
                    self.cx().scope.index_in(from, binder, telescope),
                )
            },
            Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        // An operator written as a call's head, `F(X)`, answers at that head.
        let operator = if written.is_empty() {
            origin
        }
        else {
            self.written_head(origin)
        };
        sink.origins.record_value(applied, operator);
        for &argument in written {
            let Maybe::Present(passed) = self.cx().value_at(argument)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            applied = sink.arena.value_static_application(applied, passed);
            sink.origins.record_value(applied, origin);
        }

        Maybe::Present(applied)
    }

    /// The origin of the head a call at `origin` was written with, when a
    /// call the expression grammar molds stands where a static application or
    /// an unquote is planned; `origin` itself otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the origin
    ///   [`Context::typed_heads`](gandr_surface_lowering_base::lower::Context::typed_heads)
    ///   records for the call's head when one is recorded and placed; `origin`
    ///   otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a static body's calls and a quoted carrier's call,
    ///   whose heads answer at their own spans.
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_at_a_quoted_path_carrier_unquotes_as_at_a_binder_3573`
    #[spec(ensures: |ret| ret == origin || self.cx().typed_heads.contains_key(&origin.node()))]
    fn written_head(
        &self,
        origin: Origin,
    ) -> Origin
    {
        match self
            .cx()
            .typed_heads
            .get(&origin.node())
            .map(|&head| self.cx().origin_at(head))
        {
            Some(Maybe::Present(head)) => head,
            Some(Maybe::Absent(_)) | None => origin,
        }
    }

    /// Carry out a decode's plan: the code, and the type it denotes.
    ///
    /// # Specification
    /// - requires: as [`Self::mint_code`] does.
    /// - ensures: the code [`Self::mint_code`] mints, with the written origin;
    ///   the type is the decode of that code at the universe's level, a value
    ///   type for the value sort and a computation type for the computation
    ///   sort, with the origin marked inserted; nothing when the code did not
    ///   lower.
    /// - provides: the decode half of a value name, bare or applied, in type
    ///   position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decode at each sort, of a bare code and of an
    ///   applied one, each asserted as the exact core type read back out of the
    ///   arena.
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| match (ret, universe.sort) {
            | (Maybe::Present(Lowered::ValueType(id)), GroundSort::Value) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { .. })
                )
            },
            | (Maybe::Present(Lowered::CompType(id)), GroundSort::Computation) => {
                matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { .. })
                )
            },
            | (Maybe::Absent(_), _) => true,
            | _ => false,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — decoding uses the code’s written universe when
    ///   available and marks the element node as inserted, retaining the code’s
    ///   own origin.
    /// - witness: `gandr-surface-lowering::lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `gandr-surface-lowering::lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    #[spec(
        ensures: |ret| match self.first_absent(arguments, |argument| self.cx().value_at(argument)) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => match (universe.sort, ret) {
                | (GroundSort::Value, Maybe::Present(Lowered::ValueType(id))) => {
                    sink.origins.value_type(id)
                        == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | (GroundSort::Computation, Maybe::Present(Lowered::CompType(id))) => {
                    sink.origins.comp_type(id) == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | _ => false,
            },
        },
    )]
    fn mint_decode(
        &self,
        code: Code,
        arguments: FormStretch,
        universe: Universe,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let value = match self.mint_code(code, arguments, sink, origin) {
            Maybe::Present(value) => value,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            GroundSort::Value => {
                let id = sink.arena.value_type_element(value, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            GroundSort::Computation => {
                let id = sink.arena.comp_type_element(value, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }

    /// Carry out an unquote's plan: the call of a dynamic function, the code
    /// it returns, and the type that code denotes.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: `f(v1, …, vn)` where a type is read mints as the decode of
    ///   `returned(c)`, `c` the call [`Self::mint_called`] mints, at the
    ///   universe's level, a value type for the value sort and a computation
    ///   type for the computation sort; the returned code and the decode are
    ///   marked inserted. Nothing is minted when an argument did not lower.
    /// - provides: `El` as unquote: a function from values to a universe is a
    ///   first-order function to a code, and the type it denotes is the decode
    ///   of what the call returns, which the checker reduces by running it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function of one argument, a binder holding a thunk
    ///   and a decoder's own descent called where a type is read, each asserted
    ///   as the exact core type read back out of the arena, with each node's
    ///   origin.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_to_a_universe_unquotes_where_a_type_is_read`
    /// - witness: `gandr-surface-lowering::lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => universe.sort == GroundSort::Value
                && matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(Lowered::CompType(id)) => universe.sort == GroundSort::Computation
                && matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    fn mint_unquote(
        &self,
        function: Code,
        arguments: FormStretch,
        universe: Universe,
        sink: &mut Sink<'_>,
        (origin, head): (Origin, Origin),
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let called = match self.mint_called(function, arguments, sink, (origin, head)) {
            Maybe::Present(called) => called,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let code = sink.arena.value_returned(called);
        sink.origins
            .record_value(code, origin.inserted(Insertion::Endpoint));
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            GroundSort::Value => {
                let id = sink.arena.value_type_element(code, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            GroundSort::Computation => {
                let id = sink.arena.comp_type_element(code, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }

    /// Carry out a reapplied plan: the call of a dynamic function, the value
    /// it returns forced and applied once more, the code that application
    /// returns, and the type that code denotes (#5213).
    ///
    /// # Specification
    /// - requires: every argument of both stretches is already minted or
    ///   absent.
    /// - ensures: `f(a1, …, an)(b1, …, bm)` where a type is read mints as the
    ///   decode of `returned(app(… app(force returned(c), b1) …, bm))`, `c` the
    ///   call [`Self::mint_called`] mints of the first list, at the universe's
    ///   level, a value type for the value sort and a computation type for the
    ///   computation sort. The inner returned value, the force, both returned
    ///   codes and the decode are marked inserted; each application of the
    ///   second list carries the written origin. Nothing is minted when an
    ///   argument did not lower.
    /// - provides: the type a function's result names, `a(x)` for a binder `a`
    ///   the checker instantiates at `Standard.subTy(g, d, a, s)`, as it
    ///   prints, so the printed type lowers back to itself.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function of four arguments whose result one more
    ///   argument applies, asserted as the exact core type read back out of the
    ///   arena.
    /// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => universe.sort == GroundSort::Value
                && matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(Lowered::CompType(id)) => universe.sort == GroundSort::Computation
                && matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    fn mint_reapplied(
        &self,
        function: Code,
        (arguments, again): (FormStretch, FormStretch),
        universe: Universe,
        sink: &mut Sink<'_>,
        (origin, head): (Origin, Origin),
    ) -> Maybe<Lowered, lowered::Absent>
    {
        for &argument in self.cx().operands.read(again) {
            if let Maybe::Absent(reason) = self.cx().value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        let called = match self.mint_called(function, arguments, sink, (origin, head)) {
            Maybe::Present(called) => called,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let result = sink.arena.value_returned(called);
        sink.origins
            .record_value(result, origin.inserted(Insertion::Endpoint));
        let mut applied = sink.arena.computation_force(result);
        sink.origins
            .record_computation(applied, origin.inserted(Insertion::Force));
        for &argument in self.cx().operands.read(again) {
            if let Maybe::Present(value) = self.cx().value_at(argument) {
                applied = sink.arena.computation_application(applied, value);
                sink.origins.record_computation(applied, origin);
            }
        }
        let code = sink.arena.value_returned(applied);
        sink.origins
            .record_value(code, origin.inserted(Insertion::Endpoint));
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            GroundSort::Value => {
                let id = sink.arena.value_type_element(code, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            GroundSort::Computation => {
                let id = sink.arena.comp_type_element(code, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }

    /// Carry out a dynamic call's plan: the function the code names, forced
    /// and applied to the arguments.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: `f(v1, …, vn)` mints as `app(… app(force f, v1) …, vn)`, `f`
    ///   the constant at its admission position or the variable at the binder's
    ///   index in the telescope of the type the call stands in. Each argument
    ///   is passed as it lowered: an argument a type reads as the value a call
    ///   returns, `⟨c⟩`, stays in place, so a later argument whose type reads
    ///   it meets the same value. The applications carry the written origin,
    ///   and the head carries `head`, the call's own origin or its head's where
    ///   a call the expression grammar molds stands in a type; the force is
    ///   marked inserted. Nothing is minted when an argument did not lower.
    /// - provides: the call an unquote decodes, and a type-position call's
    ///   argument written as a call, which the checker runs where it reads the
    ///   type. A descent through a function field, `el[<](b(x))`, passes
    ///   `⟨b(x)⟩` as written.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `arguments`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_unquote`], whose calls it mints, and
    ///   a call whose later argument's type reads an earlier argument's call.
    /// - witness: `gandr-surface-lowering::lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_family_over_an_applied_index_reads_the_call_in_place_5051`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(id) => matches!(
                sink.arena.computation(id),
                Some(&(gandr_core_term::Computation::Force(_) | gandr_core_term::Computation::Application(..)))
            ),
            | Maybe::Absent(_) => true,
        },
    )]
    fn mint_called(
        &self,
        function: Code,
        arguments: FormStretch,
        sink: &mut Sink<'_>,
        (origin, head_origin): (Origin, Origin),
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let written = self.cx().operands.read(arguments);
        for &argument in written {
            if let Maybe::Absent(reason) = self.cx().value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        let head = self.called_head(function, sink, head_origin);
        let mut called = sink.arena.computation_force(head);
        sink.origins
            .record_computation(called, origin.inserted(Insertion::Force));
        for &argument in written {
            if let Maybe::Present(value) = self.cx().value_at(argument) {
                called = sink.arena.computation_application(called, value);
                sink.origins.record_computation(called, origin);
            }
        }

        Maybe::Present(called)
    }

    /// The head of a dynamic call: the function the code names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the constant at its admission position, or the variable at
    ///   the binder's index in the telescope of the type the call stands in,
    ///   with the origin `head_origin`.
    /// - provides: the head that [`Self::mint_called`] and
    ///   [`Self::mint_forced`] force.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder's call and a declaration's call, each with
    ///   arguments and with none, asserted as the exact core node read back out
    ///   of the arena.
    /// - witness: `gandr-surface-lowering::lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `gandr-surface-lowering::lower::tests::a_nullary_call_at_a_family_s_argument_is_its_head_s_force_6787`
    #[spec(
        ensures: |ret| {
            sink.origins.value(ret) == Maybe::Present(head_origin)
                && matches!(
                    sink.arena.value(ret),
                    Some(&(gandr_core_term::Value::Variable { .. } | gandr_core_term::Value::Constant(_)))
                )
        },
    )]
    fn called_head(
        &self,
        function: Code,
        sink: &mut Sink<'_>,
        head_origin: Origin,
    ) -> ValueId
    {
        let head = match function {
            Code::Bound {
                from,
                binder,
                telescope,
            } => sink.arena.value_variable(
                Zone::Intuitionistic,
                self.cx().scope.index_in(from, binder, telescope),
            ),
            Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        sink.origins.record_value(head, head_origin);
        head
    }

    /// Carry out the plan of a dynamic function called with no argument where
    /// a type reads a value: the force of the function the code names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `f()` mints as `force f`, with `f` as [`Self::called_head`]
    ///   mints it. The force is the call the source writes, so it carries the
    ///   written origin `origin`. The force of the expression grammar's `f()`
    ///   carries its call's origin in the same way (#6787).
    /// - provides: a type-position call's argument written as a call with no
    ///   argument, which a value position nests.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function called with no argument at a family's
    ///   argument, in the call form and in the juxtaposed form, asserted as the
    ///   exact core node read back out of the arena, with its origin.
    /// - witness: `gandr-surface-lowering::lower::tests::a_nullary_call_at_a_family_s_argument_is_its_head_s_force_6787`
    #[spec(
        ensures: |ret| {
            matches!(sink.arena.computation(ret), Some(&gandr_core_term::Computation::Force(_)))
                && sink.origins.computation(ret) == Maybe::Present(origin)
        },
    )]
    fn mint_forced(
        &self,
        function: Code,
        sink: &mut Sink<'_>,
        (origin, head_origin): (Origin, Origin),
    ) -> ComputationId
    {
        let head = self.called_head(function, sink, head_origin);
        let forced = sink.arena.computation_force(head);
        sink.origins.record_computation(forced, origin);
        forced
    }

    /// Carry out a tuple's plan: its members, as one tuple.
    ///
    /// # Specification
    /// - requires: every member is already minted or absent.
    /// - ensures: `(v1, …, vn)` mints as one tuple of `n` components in written
    ///   order, with the written origin, so a tuple inhabits the product of as
    ///   many components that one `*` chain builds; nothing is minted when a
    ///   member did not lower.
    /// - provides: the introduction of the eager product.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `members`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of two and a tuple of four keep their members
    ///   in order as one node; the node records the tuple's origin.
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = self.cx().operands.read(members);
            match written
                .iter()
                .find_map(|&member| match self.cx().value_at(member) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::Value(id))
                        if sink.origins.value(id) == Maybe::Present(origin)
                            && sink.arena.value(id).and_then(gandr_core_term::Value::components).is_some_and(|components| components.len() == written.len()))
                },
            }
        },
    )]
    fn mint_tuple(
        &self,
        members: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = self.cx().operands.read(members);
        let mut components = Vec::with_capacity(written.len());
        for &member in written {
            match self.cx().value_at(member) {
                Maybe::Present(component) => components.push(component),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_tuple(&components);

        Maybe::Present(sink.value(id, origin))
    }

    /// Carry out a many-value return's plan: the return of its members, one
    /// value per output.
    ///
    /// # Specification
    /// - requires: every member is already minted or absent.
    /// - ensures: the many-value return of the members in written order, with
    ///   the written origin; nothing is minted when a member did not lower.
    /// - provides: the return of several values.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `members`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pair`](crate::lower::Expressions::pair).
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_tuple_ending_a_body_of_outputs_returns_each_member`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    fn mint_return_all(
        &self,
        members: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = self.cx().operands.read(members);
        let mut values = Vec::with_capacity(written.len());
        for &member in written {
            match self.cx().value_at(member) {
                Maybe::Present(value) => values.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.computation_return_all(&values);

        Maybe::Present(sink.computation(id, origin))
    }

    /// Carry out a list literal's plan: its elements, as cons cells ending in
    /// the empty list.
    ///
    /// # Specification
    /// - requires: every element is already minted or absent.
    /// - ensures: `[v1, …, vn]` mints as `n` cons cells over the elements in
    ///   written order ending in one empty list, every cell and the empty list
    ///   with the written origin, so the literal is the list `v1 :: … :: vn ::
    ///   nil` builds; nothing is minted when an element did not lower.
    /// - provides: the introduction of the native list from its elements.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each loop runs once per entry of the finite stretch `elements`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty list, a list of one and a list of three
    ///   keep their elements in order as a cons chain ending in the empty list,
    ///   whose head records the literal's origin.
    /// - witness: `gandr-surface-lowering::lower::tests::a_list_literal_lowers_to_its_cons_cells_1544`
    #[spec(
        ensures: |ret| {
            let written = self.cx().operands.read(elements);
            match written
                .iter()
                .find_map(|&element| match self.cx().value_at(element) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::Value(id))
                        if sink.origins.value(id) == Maybe::Present(origin)
                            && matches!(
                                (written.is_empty(), sink.arena.value(id)),
                                (true, Some(&gandr_core_term::Value::ListNil))
                                    | (false, Some(&gandr_core_term::Value::ListCons(..)))
                            ))
                },
            }
        },
    )]
    fn mint_list(
        &self,
        elements: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = self.cx().operands.read(elements);
        let mut heads = Vec::with_capacity(written.len());
        for &element in written {
            match self.cx().value_at(element) {
                Maybe::Present(head) => heads.push(head),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let mut list = sink.arena.value_list_nil();
        for &head in heads.iter().rev() {
            sink.origins.record_value(list, origin);
            list = sink.arena.value_list_cons(head, list);
        }

        Maybe::Present(sink.value(list, origin))
    }

    /// Carry out a product's plan: its components, as one product.
    ///
    /// # Specification
    /// - requires: every component is already minted or absent.
    /// - ensures: `A1 * … * An` mints as one product of `n` components in
    ///   written order, with the written origin; nothing is minted when a
    ///   component did not lower.
    /// - provides: the eager product type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `components`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of two and a chain of four keep their
    ///   components in order as one node, which records the product's origin.
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = self.cx().operands.read(components);
            match written
                .iter()
                .find_map(|&component| match self.cx().value_type_at(component) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id))
                        if sink.origins.value_type(id) == Maybe::Present(origin)
                            && sink.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) if parts.len() == written.len())))
                },
            }
        },
    )]
    fn mint_product(
        &self,
        components: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = self.cx().operands.read(components);
        let mut parts = Vec::with_capacity(written.len());
        for &component in written {
            match self.cx().value_type_at(component) {
                Maybe::Present(part) => parts.push(part),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_product(&parts);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a value function space's plan: the thunked arrow it is the
    /// alias of.
    ///
    /// # Specification
    /// - requires: every domain and the codomain are already minted or absent.
    /// - ensures: `(A1, …, An) -> B` mints as `+U (A1 -> … -> An -> C)`, `C`
    ///   the computation type [`Self::box_returns`] gives, every node with the
    ///   written origin, so the box and the thunked arrow it names are one core
    ///   type; nothing is minted when a domain or the codomain did not lower.
    /// - provides: the value function space.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `domains`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one domain, a list of two, and an alias nested to the
    ///   right, each asserted as the same core node the thunked arrow it stands
    ///   for lowers to.
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Thunk(_))
                )
            },
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — the box is a thunked arrow over a returner, with
    ///   domains in written order and the box's own origin.
    /// - witness: `gandr-surface-lowering::lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let missing = self.first_absent(domains, |domain| self.cx().value_type_at(domain))
                .or_else(|| match self.cx().lowered_at(codomain) {
                    | Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)) => None,
                    | Maybe::Present(_) => Some(lowered::Absent::OtherSort),
                    | Maybe::Absent(reason) => Some(reason),
                });
            match missing {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            }
        },
    )]
    fn mint_value_function(
        &self,
        domains: FormStretch,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        if let Some(reason) = self.first_absent(domains, |domain| self.cx().value_type_at(domain)) {
            return Maybe::Absent(reason);
        }
        let written = self.cx().operands.read(domains);
        let mut arrow = match self.box_returns(codomain, sink, origin) {
            Maybe::Present(arrow) => arrow,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for &domain in written.iter().rev() {
            let Maybe::Present(from) = self.cx().value_type_at(domain)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            arrow = sink.arena.comp_type_arrow(from, arrow);
            sink.origins.record_comp_type(arrow, origin);
        }
        let id = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a type former's plan.
    ///
    /// # Specification
    /// - requires: the argument position is interpreted in this lowering run.
    /// - ensures: a thunk consumes a computation type, a returner and a list
    ///   each consume a value type, and a run type consumes the session code as
    ///   a value; successful nodes carry the supplied origin.
    /// - provides: the core bridge, list or run type over the already lowered
    ///   argument.
    /// - fails: a missing or wrong-sort argument preserves its absence reason.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both bridge formers retain their argument type and
    ///   stay distinct from one another and from ordinary names with similar
    ///   spellings.
    /// - witness: `gandr-surface-lowering::lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `gandr-surface-lowering::lower::tests::u_and_f_are_names`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_run_rides_a_flow_between_sessions`
    #[spec(
        ensures: |ret| match former {
            | TypeFormer::Thunk => match self.cx().comp_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::Returner => match self.cx().value_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::CompType(id)) if sink.origins.comp_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::List => match self.cx().value_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::Run | TypeFormer::Prefix | TypeFormer::Dialogue => match self.cx().value_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
        },
    )]
    fn mint_former(
        &self,
        former: TypeFormer,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match former {
            TypeFormer::Thunk => self.cx().comp_type_at(argument).map(|inner| {
                let id = sink.arena.value_type_thunk(inner);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Returner => self.cx().value_type_at(argument).map(|inner| {
                let id = sink.arena.comp_type_returner(inner);
                sink.origins.record_comp_type(id, origin);
                Lowered::CompType(id)
            }),
            TypeFormer::List => self.cx().value_type_at(argument).map(|element| {
                let id = sink.arena.value_type_list(element);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Run => self.cx().value_at(argument).map(|session| {
                let id = sink.arena.value_type_run(session);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Prefix => self.cx().value_at(argument).map(|session| {
                let id = sink.arena.value_type_prefix(session);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Dialogue => self.cx().value_at(argument).map(|session| {
                let id = sink.arena.value_type_dialogue(session);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
        }
    }

    /// Carry out the plan of a former over already-minted children.
    ///
    /// # Specification
    /// - requires: child positions are interpreted in this lowering run.
    /// - ensures: each supported plan yields its own term or type family, with
    ///   the supplied origin on the new outer node.
    /// - provides: core constructors over children already lowered.
    /// - fails: unsupported plans are Unminted; missing or wrong-sort children
    ///   preserve the first required absence.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arrows, static products, pairs, abstraction, path
    ///   types, reflexivity and computation formers retain their distinct core
    ///   constructors and child order. These witnesses cover the admitted
    ///   fragment, not arbitrary foreign identifiers.
    /// - witness: `gandr-surface-lowering::lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `gandr-surface-lowering::lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Value(id)) => {
                matches!(*plan, Plan::StaticLambda(_) | Plan::Thunk(_) | Plan::Run(_) | Plan::Here(_) | Plan::Funext(..) | Plan::Equiv(..) | Plan::Univalence(_) | Plan::PathProduct(..) | Plan::Ua { .. } | Plan::Fill { .. } | Plan::ListNil | Plan::ListCons(..) | Plan::SessionRelated(..) | Plan::Stay(_) | Plan::Forward(_) | Plan::FunctionFlow(..) | Plan::FlowProduct(..) | Plan::Ascribed(..))
                    && sink.origins.value(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Computation(id)) => {
                matches!(*plan, Plan::Return(_) | Plan::Force(_) | Plan::Lambda(..) | Plan::Transport(..))
                    && sink.origins.computation(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(*plan, Plan::StaticPi(_, _) | Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..))
                    && sink.origins.value_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::CompType(id)) => {
                matches!(*plan, Plan::Arrow(_, _))
                    && sink.origins.comp_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Function { .. }) => false,
        },
    )]
    fn mint_over(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            Plan::Arrow(domain, codomain) => self.cx().value_type_at(domain).and_then(|from| {
                self.cx().comp_type_at(codomain).map(|to| {
                    let id = sink.arena.comp_type_arrow(from, to);
                    sink.origins.record_comp_type(id, origin);
                    Lowered::CompType(id)
                })
            }),
            Plan::StaticPi(domain, codomain) => self.cx().value_type_at(domain).and_then(|from| {
                self.cx().value_type_at(codomain).map(|to| {
                    let id = sink.arena.value_type_static_pi(from, to);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            Plan::Path(relating, carrier, left, right) => self
                .mint_identity_carrier(carrier, sink, origin)
                .and_then(|over| {
                    self.cx().value_at(left).and_then(|from| {
                        self.cx().value_at(right).map(|to| {
                            let id = match relating {
                                Relating::Path => sink.arena.value_type_path(over, from, to),
                                Relating::Bridge => sink.arena.value_type_bridge(over, from, to),
                            };
                            sink.origins.record_value_type(id, origin);
                            Lowered::ValueType(id)
                        })
                    })
                }),
            Plan::Here(point) => self.cx().value_at(point).map(|at| {
                let id = sink.arena.value_here(at);
                sink.value(id, origin)
            }),
            Plan::Funext(left, right) => self.cx().value_at(left).and_then(|first| {
                self.cx().value_at(right).map(|second| {
                    let id = sink.arena.value_funext(first, second);
                    sink.value(id, origin)
                })
            }),
            Plan::Equiv(forward, backward) => self.cx().value_at(forward).and_then(|first| {
                self.cx().value_at(backward).map(|second| {
                    let id = sink.arena.value_equiv(first, second);
                    sink.value(id, origin)
                })
            }),
            Plan::Univalence(record) => self.cx().value_at(record).map(|at| {
                let forward = gandr_core_term::identity::univalence_forward(sink.arena, at);
                let id = sink.arena.value_univalence(at, forward);
                sink.value(id, origin)
            }),
            Plan::PathProduct(first, second) => self.cx().value_at(first).and_then(|left| {
                self.cx().value_at(second).map(|right| {
                    let id = sink.arena.value_path_product(left, right);
                    sink.value(id, origin)
                })
            }),
            Plan::Ua {
                stratum,
                ref sides,
                named,
                forward,
                backward,
            } => self.cx().value_at(forward).and_then(|first| {
                self.cx().value_at(backward).map(|second| {
                    let id = sink
                        .arena
                        .value_ua(stratum, Arc::clone(sides), first, second);
                    sink.origins.record_sides(id, named);
                    sink.value(id, origin)
                })
            }),
            Plan::Fill {
                composite,
                generator,
                cells,
            } => IdentitiesRef::new(self.host_ref()).mint_fill(
                (composite, generator, cells),
                sink,
                origin,
            ),
            Plan::ListNil => {
                let id = sink.arena.value_list_nil();
                Maybe::Present(sink.value(id, origin))
            },
            Plan::ListCons(head, tail) => self.cx().value_at(head).and_then(|first| {
                self.cx().value_at(tail).map(|rest| {
                    let id = sink.arena.value_list_cons(first, rest);
                    sink.value(id, origin)
                })
            }),
            Plan::Transport(abstraction, path, value) => IdentitiesRef::new(self.host_ref())
                .mint_transport((abstraction, path, value), sink, origin),
            Plan::StaticLambda(body) => self.cx().value_at(body).map(|under| {
                let id = sink.arena.value_static_lambda(under);
                sink.value(id, origin)
            }),
            Plan::Thunk(body) => ExitsRef::new(self.host_ref())
                .mint_body(body, sink, origin)
                .map(|suspended| {
                    let id = sink.arena.value_thunk(suspended);
                    sink.value(id, origin)
                }),
            Plan::Return(value) => self.cx().value_at(value).and_then(|returned| {
                let id = sink.arena.computation_return(returned);
                let Some(&classifier) = self.cx().ascribed.get(&value)
                else {
                    return Maybe::Present(sink.computation(id, origin));
                };
                sink.origins.record_computation(id, origin);
                self.ascribed_return(id, value, classifier, sink, origin)
                    .map(|ascribed| sink.computation(ascribed, origin))
            }),
            Plan::Ascribed(value, classifier) => self.cx().value_at(value).and_then(|ascribed| {
                self.cx().value_type_at(classifier).map(|written| {
                    let frame = self.cx().reading(classifier).frame();
                    let ty = self.annotation_in_context(value, written, frame, frame, sink, origin);
                    let id = sink.arena.value_ascribe(ascribed, ty);
                    sink.value(id, origin)
                })
            }),
            Plan::Force(value) => self.cx().value_at(value).map(|forced| {
                let id = sink.arena.computation_force(forced);
                sink.computation(id, origin)
            }),
            Plan::Run(computation) => self.cx().computation_at(computation).map(|ran| {
                let id = sink.arena.value_run(ran);
                sink.value(id, origin)
            }),
            Plan::Flow(carrier, left, right) => self
                .mint_identity_carrier(carrier, sink, origin)
                .and_then(|over| {
                    self.cx().value_at(left).and_then(|from| {
                        self.cx().value_at(right).map(|to| {
                            let id = sink.arena.value_type_flow(over, from, to);
                            sink.origins.record_value_type(id, origin);
                            Lowered::ValueType(id)
                        })
                    })
                }),
            Plan::Stack(input, output) => self.cx().comp_type_at(input).and_then(|from| {
                self.cx().comp_type_at(output).map(|to| {
                    let id = sink.arena.value_type_stack(from, to);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            Plan::SessionRelated(relation, left, right, paths) => {
                self.cx().value_at(left).and_then(|from| {
                    self.cx().value_at(right).and_then(|to| {
                        let paths = match paths {
                            Some(paths) => self.cx().value_at(paths),
                            None => Maybe::Present(sink.arena.value_tuple(&[])),
                        };
                        paths.map(|paths| {
                            let id = sink.arena.value_session_related(relation, from, to, paths);
                            sink.value(id, origin)
                        })
                    })
                })
            },
            Plan::Stay(point) => self.cx().value_at(point).map(|at| {
                let id = sink.arena.value_stay(at);
                sink.value(id, origin)
            }),
            Plan::Forward(translator) => self.cx().value_at(translator).map(|map| {
                let id = sink.arena.value_forward(map);
                sink.value(id, origin)
            }),
            Plan::FunctionFlow(domain, codomain) => self.cx().value_at(domain).and_then(|into| {
                self.cx().value_at(codomain).map(|out| {
                    let id = sink.arena.value_function_flow(into, out);
                    sink.value(id, origin)
                })
            }),
            Plan::FlowProduct(first, second) => self.cx().value_at(first).and_then(|left| {
                self.cx().value_at(second).map(|right| {
                    let id = sink.arena.value_flow_product(left, right);
                    sink.value(id, origin)
                })
            }),
            Plan::Lambda(body, binder) => ExitsRef::new(self.host_ref())
                .mint_body(body, sink, origin)
                .and_then(|under| self.typed_parameter(binder, under, sink, origin))
                .map(|under| {
                    let id = sink.arena.computation_lambda(under);
                    let lowered = sink.computation(id, origin);
                    if let Maybe::Present(name) = self.cx().origin_at(binder) {
                        sink.origins.record_binder(id, name);
                    }
                    lowered
                }),
            Plan::Unplanned
            | Plan::Generic
            | Plan::ValueHole(_)
            | Plan::CompHole(_)
            | Plan::Variable(..)
            | Plan::Constant(_)
            | Plan::Primitive(_)
            | Plan::PrimitiveCall(..)
            | Plan::Interpolated(..)
            | Plan::Boolean(_)
            | Plan::Literal(_)
            | Plan::Natural(..)
            | Plan::Atom(_)
            | Plan::Sealed(_)
            | Plan::Instantiated(..)
            | Plan::Universe(_)
            | Plan::Decode(..)
            | Plan::Unquote(..)
            | Plan::Reapplied(..)
            | Plan::Carrier(..)
            | Plan::FixedCarrier(..)
            | Plan::Called(..)
            | Plan::Forced(_)
            | Plan::StaticApplication(..)
            | Plan::Tuple(_)
            | Plan::ReturnAll(_)
            | Plan::SelectedOutput { .. }
            | Plan::Plugged { .. }
            | Plan::List(_)
            | Plan::Record(_)
            | Plan::RecordUpdate(..)
            | Plan::Injection(..)
            | Plan::ValueFunction(..)
            | Plan::Telescope(..)
            | Plan::DependentArrow(..)
            | Plan::LinearArrow(..)
            | Plan::Returns(_)
            | Plan::Former(..)
            | Plan::Transparent(_)
            | Plan::Application(..)
            | Plan::Function(_)
            | Plan::Data(..)
            | Plan::Codata(..)
            | Plan::Expansion(..)
            | Plan::Constructor(_)
            | Plan::Ports(..)
            | Plan::Case(_)
            | Plan::EmptyCase(_)
            | Plan::Product(_)
            | Plan::RecordType(..)
            | Plan::Sum(..)
            | Plan::With(..)
            | Plan::Copattern(_)
            | Plan::Observe(..)
            | Plan::Select(..)
            | Plan::Field(..)
            | Plan::SubRecord(..)
            | Plan::Projected(_)
            | Plan::Block(_)
            | Plan::Loop(_)
            | Plan::While(..)
            | Plan::If(_)
            | Plan::For(..)
            | Plan::Break
            | Plan::Reenter(_)
            | Plan::Derived(_)
            | Plan::Session(..)
            | Plan::Action(..)
            | Plan::Access(_)
            | Plan::World(_)
            | Plan::Staged(..)
            | Plan::Patched { .. }
            | Plan::Kept(..)
            | Plan::TelescopeTransport(_)
            | Plan::Capability(..)
            | Plan::Effectful(..)
            | Plan::Exercise(_)
            | Plan::Method(_)
            | Plan::Scope(_)
            | Plan::Resume(..)
            | Plan::Abandon(_)
            | Plan::Recorded(_)
            | Plan::Dialogue(_)
            | Plan::Decompose(_)
            | Plan::Ride(..)
            | Plan::FlowThen(..)
            | Plan::Relation(..)
            | Plan::Bundle(_)
            | Plan::Packed(_) => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// The carrier `carrier` mints: the type written for it, the universe its
    /// tiles spell, or the decoding of the hole an omitted carrier nominates,
    /// recorded as the implicit the form omits.
    ///
    /// # Specification
    /// - requires: a written carrier's node was read as a value type.
    /// - ensures: a universe and an omitted carrier mint at once; a written one
    ///   is the type its node lowered to, or that node's absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a flow over an omitted carrier lowers to a flow over
    ///   the decoding of a nominated hole, recorded as the implicit `A` of
    ///   `Flow`.
    /// - witness: `gandr-surface-lowering::lower::identity::tests::an_omitted_carrier_is_a_nominated_hole_4932`
    #[spec(ensures: |ret| matches!(carrier, Carrier::Written(_)) || matches!(ret, Maybe::Present(_)))]
    fn mint_identity_carrier(
        &self,
        carrier: Carrier,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        match carrier {
            Carrier::Written(written) => self.cx().value_type_at(written),
            Carrier::Universe(universe) => {
                Maybe::Present(sink.arena.value_type_universe(
                    Sort::Ground(universe.sort),
                    Level::constant(universe.level),
                ))
            },
            Carrier::Omitted(hole) => {
                let code = sink.arena.value_hole(hole);
                sink.origins
                    .record_value(code, origin.inserted(Insertion::Implicit));
                if let Some(&implicit::Nomination::Omitted { function, implicit }) =
                    self.cx().nominations.get(&hole)
                {
                    sink.origins.record_omitted(code, Omitted::Implicit {
                        function: String::from(function.as_ref()),
                        implicit: String::from(implicit.as_ref()),
                    });
                }
                Maybe::Present(
                    sink.arena
                        .value_type_element(code, Level::constant(LevelConstant::ZERO)),
                )
            },
        }
    }

    /// `written`, an annotation's type read under `from`, carried under `to`
    /// into the context the annotated term at `term` reads its names in.
    ///
    /// A name inside a type counts in the type's telescope, so an annotation
    /// whose term lies in a type stays in that telescope. A term in a body
    /// reads its names in the body's context, which binds every binder, and
    /// the annotation is carried there (#662).
    ///
    /// # Specification
    /// - requires: `written` is minted under `from`, counting only the frames
    ///   that bind in the signature's telescope, or in a body quote's when
    ///   `term` lies in one; `from` is `to` or a frame of `to`'s chain.
    /// - ensures: when `term` lies in a type, `written` lifted past the frames
    ///   between `from` and `to` that bind in the type's telescope
    ///   ([`NativeRef::lift_value_type`]), so `written` itself when `from` is
    ///   `to`; otherwise `written` carried into the term context of `to`, as
    ///   [`NativeRef::carry_value_type`] carries it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ascription, a typed bind and a typed parameter
    ///   inside a type, under a parameter the type does not name, each keep
    ///   their annotation's indices; one in a body is carried past that
    ///   parameter.
    /// - witness: `gandr-surface-lowering::lower::identity::tests::an_annotation_inside_a_type_reads_in_the_type_s_telescope_3801`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotated_return_is_ascribed_its_returner_1107`
    #[spec(ensures: |ret| !self.cx().in_type.contains(&term) || from != to || ret == written)]
    fn annotation_in_context(
        &self,
        term: NodeIndex,
        written: ValueTypeId,
        from: Frame,
        to: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        if self.cx().in_type.contains(&term) {
            let telescope = self.telescope_at(term);
            return NativeRef::over(self.cx())
                .lift_value_type(written, from, telescope, to, sink, origin);
        }
        NativeRef::over(self.cx()).carry_value_type(
            written,
            from,
            Telescope::Signature,
            to,
            sink,
            origin,
        )
    }

    /// `returned`, the return of the annotated value at `term`, ascribed the
    /// returner of the annotation's type `classifier`.
    ///
    /// # Specification
    /// - requires: `classifier` was read as a value type under the frame the
    ///   return stands in, and is minted.
    /// - ensures: `(returned : -F T)`, `T` carried into the context `term`
    ///   reads its names in, as a typed bind's annotation is
    ///   ([`Self::annotation_in_context`]), and its returner minted at
    ///   `origin`; the ascription itself is left for the caller to record.
    /// - fails: the type's absence where it was not minted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written return and a tail's inferred one, each
    ///   ascribed alike.
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotated_return_is_ascribed_its_returner_1107`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) => matches!(sink.arena.computation(id), Some(&Computation::Ascribe { body, .. }) if body == returned),
        | Maybe::Absent(_) => true,
    })]
    fn ascribed_return(
        &self,
        returned: ComputationId,
        term: NodeIndex,
        classifier: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.cx().value_type_at(classifier).map(|written| {
            let frame = self.cx().reading(classifier).frame();
            let result = self.annotation_in_context(term, written, frame, frame, sink, origin);
            let returner = sink.arena.comp_type_returner(result);
            sink.origins.record_comp_type(returner, origin);
            sink.arena.computation_ascribe(returned, returner)
        })
    }

    /// `under`, the body of the lambda whose parameter is `binder`, beneath
    /// the bind that holds the argument to the parameter's written type:
    /// where the parameter is written with its type `A`, `(return #0 : -F A)
    /// to _. under`. The parameter is the lambda's own binder, so a type that
    /// reads the lambda's binder reads the parameter (#3735).
    ///
    /// # Specification
    /// - requires: `under` is minted beneath a typed parameter's bind, its
    ///   frame one unnamed binder past the lambda's own; `A` was read as a
    ///   value type where the lambda stands.
    /// - ensures: `under` itself for a parameter written without a type;
    ///   otherwise the bind of the argument, returned and ascribed the returner
    ///   of `A` carried into the term context of the lambda's frame, over
    ///   `under`, every node minted at `origin` marked as the parameter's
    ///   insertion.
    /// - fails: the written type's absence where it was not minted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::lambda`](crate::lower::Expressions::lambda).
    /// - witness: `gandr-surface-lowering::lower::tests::a_typed_parameter_binds_its_argument_ascribed_1310`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) if self.cx().typed_parameters.contains_key(&binder) => {
            matches!(sink.arena.computation(id), Some(&Computation::Bind(_, rest)) if rest == under)
        },
        | Maybe::Present(id) => id == under,
        | Maybe::Absent(_) => self.cx().typed_parameters.contains_key(&binder),
    })]
    fn typed_parameter(
        &self,
        binder: NodeIndex,
        under: ComputationId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let Some(&(declared, read, parameter)) = self.cx().typed_parameters.get(&binder)
        else {
            return Maybe::Present(under);
        };
        self.cx().value_type_at(declared).map(|written| {
            let inserted = origin.inserted(Insertion::Parameter);
            let declared =
                self.annotation_in_context(binder, written, read, parameter, sink, inserted);
            let returner = sink.arena.comp_type_returner(declared);
            sink.origins.record_comp_type(returner, inserted);
            let passed = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            sink.origins.record_value(passed, inserted);
            let returned = sink.arena.computation_return(passed);
            sink.origins.record_computation(returned, inserted);
            let ascribed = sink.arena.computation_ascribe(returned, returner);
            sink.origins.record_computation(ascribed, inserted);
            let bound = sink.arena.computation_bind(ascribed, under);
            sink.origins.record_computation(bound, inserted);
            bound
        })
    }

    /// Mint a block: its statements bound over its last computation.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent.
    /// - ensures: `let x1 = c1 ; … let xn = cn ; c` mints as `bind(c1, …
    ///   bind(cn, c))`, each bind's origin its statement's `let` tile, and a
    ///   typed `let x : A = c ;` binds `c` ascribed the pure `-F A`; a tuple
    ///   `let (x, …) = c ;` splits what `c` returns, each component the pattern
    ///   writes recorded as the name of the split's binder at its place
    ///   ([`OriginTable::component`]); a fork `let d = fork (c : S) t;` mints
    ///   as the fork of `t` at `S` whose parent is the rest of the block, at
    ///   its `let` tile's origin; a hold `var x = e ;` mints as the hold of `e`
    ///   whose scope is the rest of the block, at its keyword's origin; a `let
    ///   x at w = v ;` mints as the opening of `v` at `w` whose body is the
    ///   rest of the block, at the statement's origin, binding the name; a `let
    ///   x = v ;` mints as `bind(return v, …)` over the rest of the block at
    ///   the `let`'s origin, or as the bind of the computation nested in `v`
    ///   when no type is stated; a block of no statements is its last
    ///   computation; nothing is minted when any computation, value or protocol
    ///   of the block did not lower.
    /// - provides: the block half of thunks, lambdas and function tails.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `let` statements wrap the final computation in source
    ///   order, each bind records its `let` token, and an empty statement
    ///   prefix leaves the existing final computation unchanged.
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `gandr-surface-lowering::lower::tests::a_let_binds_a_value_once_and_a_computation_nested`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tuple_binder_names_each_component_it_writes_2181`
    /// - witness: `gandr-surface-lowering::lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match self.cx().computation_at(block.last) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(last) => {
                let statements = self.cx().statements.read(block.statements);
                let missing = statements.iter().find_map(|statement| {
                    match (self.statement_parts(statement), self.cx().origin_at(statement.origin)) {
                        | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => Some(reason),
                        | (Maybe::Present(()), Maybe::Present(_)) => None,
                    }
                });
                match missing {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None => match statements.first() {
                        | None => ret == Maybe::Present(last),
                        | Some(first) => {
                            matches!(ret, Maybe::Present(id) if matches!((sink.origins.computation(id), self.cx().origin_at(first.origin)), (Maybe::Present(stored), Maybe::Present(expected)) if stored == expected))
                        },
                    },
                }
            },
        },
    )]
    #[inline]
    pub fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let statements = self.cx().statements.read(block.statements);
        let mut chain = match self.cx().computation_at(block.last) {
            Maybe::Present(last) => last,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for statement in statements {
            if let Maybe::Absent(reason) = self.statement_parts(statement) {
                return Maybe::Absent(reason);
            }
            if let Maybe::Absent(reason) = self.cx().origin_at(statement.origin) {
                return Maybe::Absent(reason);
            }
        }
        for statement in statements.iter().rev() {
            let Maybe::Present(origin) = self.cx().origin_at(statement.origin)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            if let StatementBinding::Held {
                value,
                grade,
                name,
                stated,
            } = statement.binding
            {
                let held_at = value;
                let Maybe::Present(mut value) = self.cx().value_at(value)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                if let Maybe::Present(stated) = stated {
                    let Maybe::Present(written) = self.cx().value_type_at(stated)
                    else {
                        return Maybe::Absent(lowered::Absent::Unminted);
                    };
                    // The type was read in the signature's telescope; the
                    // value it ascribes stands in the body.
                    let frame = self.cx().reading(stated).frame();
                    let held =
                        self.annotation_in_context(held_at, written, frame, frame, sink, origin);
                    value = sink.arena.value_ascribe(value, held);
                    sink.origins.record_value(value, origin);
                }
                let id = sink.arena.computation_memory(MemoryForm::Hold {
                    value,
                    body: chain,
                    grade,
                });
                sink.origins.record_computation(id, origin);
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(id, name);
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Located { annotation, name } = statement.binding {
                let (Maybe::Present(value), Maybe::Present(written)) = (
                    self.cx().value_at(statement.bound),
                    self.cx().value_type_at(annotation),
                )
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let frame = self.cx().reading(annotation).frame();
                let located = self.annotation_in_context(
                    statement.bound,
                    written,
                    frame,
                    frame,
                    sink,
                    origin,
                );
                let held = sink.arena.computation_world(WorldForm::Hold { value });
                sink.origins.record_computation(held, origin);
                let returner = sink.arena.comp_type_returner(located);
                sink.origins.record_comp_type(returner, origin);
                let ascribed = sink.arena.computation_ascribe(held, returner);
                sink.origins.record_computation(ascribed, origin);
                let id = sink.arena.computation_bind(ascribed, chain);
                sink.origins.record_computation(id, origin);
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(id, name);
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Opened { value, name, world } = statement.binding {
                let Maybe::Present(value) = self.cx().value_at(value)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let id = sink.arena.computation_world(WorldForm::Leta {
                    world,
                    value,
                    body: chain,
                });
                sink.origins.record_computation(id, origin);
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(id, name);
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Forked {
                protocol,
                child,
                end,
            } = statement.binding
            {
                let (Maybe::Present(protocol), Maybe::Present(child)) = (
                    self.cx().value_type_at(protocol),
                    self.cx().computation_at(child),
                )
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let id = sink.arena.computation_session(SessionAction::Fork {
                    protocol,
                    child,
                    parent: chain,
                });
                sink.origins.record_computation(id, origin);
                if let Some(name) = self.cx().tree.fragment(end) {
                    sink.origins
                        .record_fork(id, ChannelName::from(String::from(name.as_ref())));
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Received {
                endpoint,
                subject,
                name,
            } = statement.binding
            {
                let id = sink.arena.computation_session(SessionAction::Receive {
                    endpoint,
                    body: chain,
                });
                sink.origins.record_computation(id, origin);
                sink.origins.record_label(Label {
                    span: subject,
                    labelled: Labelled::Endpoint(id),
                });
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(id, name);
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Let(name) | StatementBinding::TypedLet { name, .. } =
                statement.binding
            {
                let Maybe::Present(value) = self.let_value(statement, sink, origin)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                // A value is returned once and bound: the checker reads the
                // name as the value. A call nested there with no stated type
                // runs where the statement stands when it returns, and is
                // suspended otherwise. Any other computation nested there with
                // no stated type runs once, where it is bound; under a stated
                // type, the type decides.
                let returned = match (statement.binding, sink.arena.value(value)) {
                    (StatementBinding::Let(_), Some(&Value::Nested(nested)))
                        if !matches!(
                            sink.arena.computation(nested),
                            Some(
                                &(gandr_core_term::Computation::Application(..)
                                    | gandr_core_term::Computation::Force(_))
                            )
                        ) =>
                    {
                        nested
                    },
                    _ => {
                        let returned = sink.arena.computation_return(value);
                        sink.origins
                            .record_computation(returned, origin.inserted(Insertion::Return));
                        returned
                    },
                };
                let id = sink.arena.computation_bind(returned, chain);
                sink.origins.record_computation(id, origin);
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(id, name);
                    // A binder over a nested call answers at what the call
                    // returns, as a run binder does, though a rewrite of the
                    // block may leave no bind naming it (#298).
                    if matches!(sink.arena.value(value), Some(&Value::Nested(_))) {
                        sink.origins.record_label(Label {
                            span: name.span(),
                            labelled: Labelled::Bound(statement.bound),
                        });
                    }
                }
                chain = id;
                continue;
            }
            let Maybe::Present(bound) = self.cx().computation_at(statement.bound)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let split = match statement.binding {
                StatementBinding::Named(_)
                | StatementBinding::Placed(_)
                | StatementBinding::Let(_)
                | StatementBinding::TypedLet { .. }
                | StatementBinding::Typed { .. }
                | StatementBinding::Opening { .. }
                | StatementBinding::Forked { .. }
                | StatementBinding::Received { .. }
                | StatementBinding::Held { .. }
                | StatementBinding::Located { .. }
                | StatementBinding::Opened { .. }
                | StatementBinding::Outputs { .. } => None,
                StatementBinding::Discarded => Some(gandr_core_term::ComponentCount::default()),
                StatementBinding::Split { arity, .. }
                | StatementBinding::TypedSplit { arity, .. } => Some(arity),
            };
            if let Some(arity) = split {
                let tuple = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(tuple, origin);
                let split = sink.arena.computation_split(tuple, arity, chain);
                sink.origins.record_computation(split, origin);
                // Each component a tuple pattern writes names the binder the
                // split opens for it, so a component nothing reads is still
                // where its pattern writes it.
                if let StatementBinding::Split { pattern, .. }
                | StatementBinding::TypedSplit { pattern, .. } = statement.binding
                {
                    let mut pieces = Pieces::new();
                    if read_pieces(self.cx().pbg, self.cx().tree, pattern, &mut pieces).is_ok() {
                        let written = pieces.pieces.iter().filter_map(|piece| match *piece {
                            Piece::Operand(operand) => Some(operand),
                            Piece::Tile { .. } => None,
                        });
                        for (component, operand) in written.enumerate() {
                            if let Maybe::Present(named) = self.cx().origin_at(operand.node) {
                                sink.origins.place_component(
                                    split,
                                    SplitComponent::from(component),
                                    ComponentName::Written(named),
                                );
                            }
                        }
                    }
                }
                chain = split;
            }
            if let StatementBinding::Placed(name) = statement.binding {
                // The reply's binder holds the buffer; the rest of the block
                // holds it live under the name's linear binder.
                let reply = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(reply, origin);
                let placed = sink.arena.computation_session(SessionAction::Place {
                    payload: reply,
                    body: chain,
                });
                sink.origins.record_computation(placed, origin);
                if let Maybe::Present(name) = self.cx().origin_at(name) {
                    sink.origins.record_binder(placed, name);
                }
                chain = placed;
            }
            let bound = match statement.binding {
                StatementBinding::Typed { annotation, .. }
                | StatementBinding::TypedSplit { annotation, .. } => {
                    let Maybe::Present(written) = self.cx().value_type_at(annotation)
                    else {
                        return Maybe::Absent(lowered::Absent::Unminted);
                    };
                    // The annotation was read as a type, in the signature's
                    // telescope; the computation it ascribes stands in the
                    // body, whose context binds every binder (#662), or in a
                    // type, whose telescope it shares.
                    let frame = self.cx().reading(annotation).frame();
                    let result = self.annotation_in_context(
                        statement.bound,
                        written,
                        frame,
                        frame,
                        sink,
                        origin,
                    );
                    let returner = sink.arena.comp_type_returner(result);
                    sink.origins.record_comp_type(returner, origin);
                    let ascribed = sink.arena.computation_ascribe(bound, returner);
                    sink.origins.record_computation(ascribed, origin);
                    ascribed
                },
                StatementBinding::Opening { stated, frame, .. } => {
                    let Maybe::Present(written) = self.cx().value_type_at(stated)
                    else {
                        return Maybe::Absent(lowered::Absent::Unminted);
                    };
                    // The model type was read where `p` is declared, a frame
                    // of the statement's chain; the ascription stands in the
                    // statement's body context.
                    let result = self.annotation_in_context(
                        statement.bound,
                        written,
                        self.cx().reading(stated).frame(),
                        frame,
                        sink,
                        origin,
                    );
                    let returner = sink.arena.comp_type_returner(result);
                    sink.origins.record_comp_type(returner, origin);
                    let ascribed = sink.arena.computation_ascribe(bound, returner);
                    sink.origins.record_computation(ascribed, origin);
                    ascribed
                },
                StatementBinding::Named(_)
                | StatementBinding::Placed(_)
                | StatementBinding::Let(_)
                | StatementBinding::TypedLet { .. }
                | StatementBinding::Discarded
                | StatementBinding::Split { .. }
                | StatementBinding::Outputs { .. }
                | StatementBinding::Forked { .. }
                | StatementBinding::Received { .. }
                | StatementBinding::Held { .. }
                | StatementBinding::Located { .. }
                | StatementBinding::Opened { .. } => bound,
            };
            // A call's outputs bind one binder each, the first outermost.
            let id = if let StatementBinding::Outputs { arity, .. } = statement.binding {
                sink.arena.computation_bind_all(bound, arity, chain)
            }
            else {
                sink.arena.computation_bind(bound, chain)
            };
            sink.origins.record_computation(id, origin);
            if let StatementBinding::Named(name)
            | StatementBinding::Placed(name)
            | StatementBinding::Typed { name, .. }
            | StatementBinding::Opening { name, .. } = statement.binding
                && let Maybe::Present(name) = self.cx().origin_at(name)
            {
                sink.origins.record_binder(id, name);
            }
            // Each output's binder names the binder the bind opens for it, so
            // a binder nothing reads is still where its pattern writes it.
            if let StatementBinding::Outputs { pattern, .. } = statement.binding
                && let Some(binders) = self.cx().output_binders.get(&pattern)
            {
                for (output, &binder) in binders.iter().enumerate() {
                    if let Maybe::Present(named) = self.cx().origin_at(binder) {
                        sink.origins.place_component(
                            id,
                            SplitComponent::from(output),
                            ComponentName::Written(named),
                        );
                    }
                }
            }
            // A binder, or a tuple pattern, answers at what its bound
            // computation returns, read where the run judged that
            // computation: a rewrite of the block may leave no bind and no
            // use naming it (#298). A value the statement returns, as
            // `let (y, z) = (1, 2);` writes, answers at the value's type, since
            // the source writes no computation there (#4466).
            if let StatementBinding::Named(written)
            | StatementBinding::Placed(written)
            | StatementBinding::Typed { name: written, .. }
            | StatementBinding::Opening { name: written, .. }
            | StatementBinding::Split {
                pattern: written, ..
            }
            | StatementBinding::TypedSplit {
                pattern: written, ..
            }
            | StatementBinding::Outputs {
                pattern: written, ..
            } = statement.binding
                && let Maybe::Present(written) = self.cx().origin_at(written)
            {
                let labelled = if let Maybe::Present(raw) =
                    self.cx().computation_at(statement.bound)
                    && let Some(&Computation::Return(value)) = sink.arena.computation(raw)
                {
                    Labelled::Value(value)
                }
                else {
                    Labelled::Bound(statement.bound)
                };
                sink.origins.record_label(Label {
                    span: written.span(),
                    labelled,
                });
            }
            if statement.rest == exits::Rest::Distributed {
                let _first = sink.distributed.insert(id, origin);
            }
            chain = id;
        }

        Maybe::Present(chain)
    }

    /// Whether every node a statement mints from lowered: a fork's protocol
    /// and child, a hold's or an opening's value, nothing of a receive's, and
    /// every other statement's bound computation.
    ///
    /// # Specification
    /// - requires: the statement's nodes are minted or absent.
    /// - ensures: present when they lowered at their sorts; the first absence
    ///   otherwise, the protocol's before the child's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block holding a fork and one holding a run, each
    ///   minted whole.
    /// - witness: `gandr-surface-lowering::lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `gandr-surface-lowering::lower::tests::a_block_binds_each_statement_over_the_next`
    #[spec(ensures: |ret| match statement.binding {
        | StatementBinding::Forked { protocol, child, .. } => (ret == Maybe::Present(())) == (matches!(self.cx().value_type_at(protocol), Maybe::Present(_)) && matches!(self.cx().computation_at(child), Maybe::Present(_))),
        | StatementBinding::Received { .. } => ret == Maybe::Present(()),
        | StatementBinding::Held { value, stated: Maybe::Absent(_), .. } | StatementBinding::Opened { value, .. } => (ret == Maybe::Present(())) == matches!(self.cx().value_at(value), Maybe::Present(_)),
        | StatementBinding::Held { value, stated: Maybe::Present(stated), .. } => (ret == Maybe::Present(())) == (matches!(self.cx().value_at(value), Maybe::Present(_)) && matches!(self.cx().value_type_at(stated), Maybe::Present(_))),
        | StatementBinding::Let(_) => (ret == Maybe::Present(())) == matches!(self.cx().value_at(statement.bound), Maybe::Present(_)),
        | StatementBinding::TypedLet { annotation, .. } | StatementBinding::Located { annotation, .. } => (ret == Maybe::Present(())) == (matches!(self.cx().value_at(statement.bound), Maybe::Present(_)) && matches!(self.cx().value_type_at(annotation), Maybe::Present(_))),
        | StatementBinding::Typed { annotation, .. } | StatementBinding::TypedSplit { annotation, .. } | StatementBinding::Opening { stated: annotation, .. } => (ret == Maybe::Present(())) == (matches!(self.cx().computation_at(statement.bound), Maybe::Present(_)) && matches!(self.cx().value_type_at(annotation), Maybe::Present(_))),
        | _ => (ret == Maybe::Present(())) == matches!(self.cx().computation_at(statement.bound), Maybe::Present(_)),
    })]
    fn statement_parts(
        &self,
        statement: &Statement,
    ) -> Maybe<(), lowered::Absent>
    {
        match statement.binding {
            StatementBinding::Forked {
                protocol, child, ..
            } => self
                .cx()
                .value_type_at(protocol)
                .and_then(|_protocol| self.cx().computation_at(child))
                .map(|_child| ()),
            StatementBinding::Received { .. } => Maybe::Present(()),
            StatementBinding::Held {
                value,
                stated: Maybe::Present(stated),
                ..
            } => self
                .cx()
                .value_at(value)
                .and_then(|_value| self.cx().value_type_at(stated))
                .map(|_stated| ()),
            StatementBinding::Held {
                value,
                stated: Maybe::Absent(_),
                ..
            }
            | StatementBinding::Opened { value, .. } => self.cx().value_at(value).map(|_value| ()),
            StatementBinding::Let(_) => self.cx().value_at(statement.bound).map(|_value| ()),
            StatementBinding::TypedLet { annotation, .. }
            | StatementBinding::Located { annotation, .. } => self
                .cx()
                .value_at(statement.bound)
                .and_then(|_value| self.cx().value_type_at(annotation))
                .map(|_annotation| ()),
            StatementBinding::Typed { annotation, .. }
            | StatementBinding::TypedSplit { annotation, .. }
            | StatementBinding::Opening {
                stated: annotation, ..
            } => self
                .cx()
                .computation_at(statement.bound)
                .and_then(|_bound| self.cx().value_type_at(annotation))
                .map(|_annotation| ()),
            StatementBinding::Named(_)
            | StatementBinding::Placed(_)
            | StatementBinding::Discarded
            | StatementBinding::Split { .. }
            | StatementBinding::Outputs { .. } => {
                self.cx().computation_at(statement.bound).map(|_bound| ())
            },
        }
    }

    /// The value a `let` returns: its minted value, ascribed its stated type
    /// when one is written.
    ///
    /// # Specification
    /// - requires: `statement` is a `let` over a value, its value and its
    ///   stated type minted or absent.
    /// - ensures: the value; for a stated type, the value ascribed that type
    ///   carried into the body's context, every node minted at `origin`;
    ///   nothing when a part did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::let_statement`](crate::lower::Expressions::let_statement).
    /// - witness: `gandr-surface-lowering::lower::tests::a_let_binds_a_value_once_and_a_computation_nested`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value(id).is_some()))]
    fn let_value(
        &self,
        statement: &Statement,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        let Maybe::Present(value) = self.cx().value_at(statement.bound)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let StatementBinding::TypedLet { annotation, .. } = statement.binding
        else {
            return Maybe::Present(value);
        };
        let Maybe::Present(written) = self.cx().value_type_at(annotation)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        // The type was read in the signature's telescope; the value it
        // ascribes stands in the body, whose context binds every binder.
        let frame = self.cx().reading(annotation).frame();
        let stated =
            self.annotation_in_context(statement.bound, written, frame, frame, sink, origin);
        let ascribed = sink.arena.value_ascribe(value, stated);
        sink.origins.record_value(ascribed, origin);

        Maybe::Present(ascribed)
    }

    /// Mint an application of `head` to `arguments`, left to right.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `c(v1, …, vn)` mints as `app(… app(c, v1) …, vn)`, every
    ///   application carrying the call's origin; an argument the call omits for
    ///   an implicit is the hole nominated for it
    ///   ([`Context::nominated`](gandr_surface_lowering_base::lower::Context::nominated)),
    ///   and one it omits for an instance the variable of the instance resolved
    ///   for it ([`Context::instanced`](gandr_surface_lowering_base::lower::Context::instanced)),
    ///   each marked as an implicit's insertion; a call through a joint
    ///   fixpoint passes its first argument injected at the called member's
    ///   summand, the injection marked as the fixpoint's insertion, and its
    ///   later arguments as written; a standing supply passing `k` explicit
    ///   parameters as the variables of the lambdas it opens
    ///   ([`Context::abstracted`](gandr_surface_lowering_base::lower::Context::abstracted))
    ///   mints `λ … λ. app(…)`, `k` lambdas marked as an implicit's insertion
    ///   over the application of the head and every other argument raised past
    ///   them; a call of no arguments is its head's own computation; nothing is
    ///   minted when the head or a written argument did not lower.
    /// - provides: the curried elimination of a lambda.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — applications associate to the left, force a value
    ///   head only once when required, and preserve authored versus inserted
    ///   origins.
    /// - witness: `gandr-surface-lowering::lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    /// - witness: `gandr-surface-lowering::lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::an_omitted_implicit_is_a_nominated_hole`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_standing_supply_opens_a_lambda_per_explicit_before_it_1498`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_module_supplied_for_a_model_implicit_passes_its_members_739`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::an_omitted_instance_is_the_one_handled_in_scope_2271`
    #[spec(
        captures: (written, opened, supplied) = {
            let positions = self.spread(arguments);
            let keys = || (positions.start .. positions.end).filter_map(|position| self.cx().operands.locate(At::from(position)));
            (
                (positions.start .. positions.end)
                    .filter(|&position| self.cx().operands.locate(At::from(position)).is_none_or(|key| !self.cx().nominated.contains_key(&key) && !self.cx().abstracted.contains_key(&key) && !self.cx().instanced.contains_key(&key) && !self.cx().components.contains_key(&key)))
                    .filter_map(|position| self.cx().operands.entries().get(position).copied())
                    .collect::<Vec<_>>(),
                keys().any(|key| self.cx().abstracted.contains_key(&key)),
                keys().any(|key| self.cx().components.contains_key(&key)),
            )
        },
        ensures: |ret| match self.cx().computation_at(head) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(called) => {
                match written
                    .iter()
                    .find_map(|&argument| match self.cx().value_at(argument) {
                        | Maybe::Present(_) => None,
                        | Maybe::Absent(reason) => Some(reason),
                    }) {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None if supplied && ret == Maybe::Absent(lowered::Absent::Unminted) => true,
                    | None if arguments == FormStretch::default() => {
                        ret == Maybe::Present(Lowered::Computation(called))
                    },
                    | None if opened => {
                        matches!(ret, Maybe::Present(Lowered::Computation(id)) if sink.origins.computation(id) == Maybe::Present(origin.inserted(Insertion::Implicit)))
                    },
                    | None => {
                        matches!(ret, Maybe::Present(Lowered::Computation(id)) if sink.origins.computation(id) == Maybe::Present(origin))
                    },
                }
            },
        },
    )]
    fn mint_application(
        &self,
        head: NodeIndex,
        arguments: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut applied = match self.cx().computation_at(head) {
            Maybe::Present(called) => called,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let positions = self.spread(arguments);
        let key = |position: usize| self.cx().operands.locate(At::from(position));
        for position in positions.start .. positions.end {
            if key(position).is_none_or(|key| {
                !self.cx().nominated.contains_key(&key)
                    && !self.cx().abstracted.contains_key(&key)
                    && !self.cx().instanced.contains_key(&key)
                    && !self.cx().components.contains_key(&key)
            }) && let Some(&argument) = self.cx().operands.entries().get(position)
                && let Maybe::Absent(reason) = self.cx().value_at(argument)
            {
                return Maybe::Absent(reason);
            }
        }
        let opened = (positions.start .. positions.end)
            .filter_map(key)
            .filter(|key| self.cx().abstracted.contains_key(key))
            .count();
        let under = Binders::from(u32::try_from(opened).unwrap_or(u32::MAX));
        if opened > 0 {
            applied =
                gandr_core_term::shift_computation_under(sink.arena, applied, Binders::NONE, under)
                    .settle(sink.arena);
        }
        for position in positions.start .. positions.end {
            let held = key(position);
            let mut passed = if let Some(&hole) = held.and_then(|key| self.cx().nominated.get(&key))
            {
                let id = sink.arena.value_hole(hole);
                sink.origins
                    .record_value(id, origin.inserted(Insertion::Implicit));
                match self.cx().nominations.get(&hole) {
                    Some(&implicit::Nomination::Omitted { function, implicit }) => {
                        let function = String::from(function.as_ref());
                        let implicit = String::from(implicit.as_ref());
                        sink.origins.record_omitted(
                            id,
                            match self.cx().model_candidates.get(&hole) {
                                Some(candidates) => Omitted::Model {
                                    function,
                                    implicit,
                                    candidates: candidates.clone(),
                                },
                                None => Omitted::Implicit { function, implicit },
                            },
                        );
                    },
                    Some(
                        &(implicit::Nomination::Wildcard
                        | implicit::Nomination::Spliced(_)
                        | implicit::Nomination::Answering { .. }),
                    )
                    | None => {},
                }
                id
            }
            else if let Some(&(ref supplied, place)) =
                held.and_then(|key| self.cx().components.get(&key))
            {
                match ModelsRef::new(self.host_ref())
                    .mint_supplied(supplied, place, under, sink, origin)
                {
                    Maybe::Present(id) => id,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                }
            }
            else if let Some(&index) = held.and_then(|key| self.cx().abstracted.get(&key)) {
                let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                sink.origins
                    .record_value(id, origin.inserted(Insertion::Implicit));
                id
            }
            else if let Some(&index) = held.and_then(|key| self.cx().instanced.get(&key)) {
                let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                sink.origins
                    .record_value(id, origin.inserted(Insertion::Implicit));
                if opened > 0 {
                    gandr_core_term::shift_value(sink.arena, id, under).settle(sink.arena)
                }
                else {
                    id
                }
            }
            else {
                match self
                    .cx()
                    .operands
                    .entries()
                    .get(position)
                    .map(|&argument| self.cx().value_at(argument))
                {
                    Some(Maybe::Present(passed)) if opened > 0 => {
                        gandr_core_term::shift_value(sink.arena, passed, under).settle(sink.arena)
                    },
                    Some(Maybe::Present(passed)) => passed,
                    Some(Maybe::Absent(reason)) => return Maybe::Absent(reason),
                    None => return Maybe::Absent(lowered::Absent::Unminted),
                }
            };
            // A call through a joint injects the argument its member stages,
            // the first; the later ones pass as written.
            if position == positions.start
                && let Some(&summand) = self.cx().injected.get(&head)
            {
                let injected = sink.arena.value_injection(summand, passed);
                sink.origins
                    .record_value(injected, origin.inserted(Insertion::Fixpoint));
                passed = injected;
            }
            let id = sink.arena.computation_application(applied, passed);
            sink.origins.record_computation(id, origin);
            applied = id;
        }
        for _ in 0 .. opened {
            let id = sink.arena.computation_lambda(applied);
            sink.origins
                .record_computation(id, origin.inserted(Insertion::Implicit));
            applied = id;
        }

        Maybe::Present(Lowered::Computation(applied))
    }

    /// Mint a function tail: its body, and its declared type when it states
    /// one.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `(x1: A1, …, xn: An) -> C { b }` mints its body as `thunk (λ
    ///   … λ. b)`, one lambda per parameter with the binder tile's origin and
    ///   the thunk marked as inserted at the declaration form; a recursive tail
    ///   closes its staged parameter's lambda by a fixpoint marked as inserted
    ///   at the declaration form, its binder named where the function's own
    ///   name is written, `thunk (λ … λ. fix. λ … λ. b)`, and a recursive tail
    ///   of no parameter its body, `thunk (fix. b)`, claiming structural
    ///   descent when a call claims it and partial otherwise; a written-through
    ///   method's `b` runs under the hold of its receiver
    ///   [`Capability::hold_body`](method::hold_body) mints, and a body whose
    ///   parameters stand at a session type under their placements
    ///   [`CapabilityRef::place_body`] mints, outside the hold; its declared
    ///   type is `+U (A1 -> … -> An -> C)`, one arrow per parameter with the
    ///   binder tile's origin and `+U` the declaration form's, an arrow
    ///   dependent where a later type names its parameter, and a
    ///   written-through method's `C` the `F (T × R)`
    ///   [`CapabilityRef::written_result`] mints; a tail missing a parameter or
    ///   result type mints the body alone; nothing is minted when the block did
    ///   not lower.
    /// - provides: the function tail's two halves, from one reading.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — function tails produce an inserted thunk over their
    ///   lambda chain even when a missing parameter or result type prevents a
    ///   signature.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    /// - witness: `gandr-surface-lowering::lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterless_recursive_tail_binds_its_own_name_1499`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Function { signature, body }) => {
                sink.origins.value(body) == Maybe::Present(origin.inserted(Insertion::Thunk))
                    && match signature {
                        | Maybe::Absent(_) => true,
                        | Maybe::Present(id) => {
                            sink.origins.value_type(id) == Maybe::Present(origin)
                        },
                    }
            },
            | Maybe::Present(_) => false,
        },
    )]
    fn mint_function(
        &self,
        function: &Function,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let parameters = self.cx().parameters.read(function.parameters);
        for parameter in parameters {
            if let Maybe::Absent(reason) = self.cx().origin_at(parameter.binder) {
                return Maybe::Absent(reason);
            }
        }
        let minted = match function.body {
            Body::Block(block) => ExitsRef::new(self.host_ref()).mint_body(block, sink, origin),
            Body::Clauses(case) => match NativeRef::over(self.cx()).mint_case(case, sink, origin) {
                Maybe::Present(Lowered::Computation(tree)) => Maybe::Present(tree),
                Maybe::Present(_) => Maybe::Absent(lowered::Absent::Unminted),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
        };
        let mut body = match minted {
            Maybe::Present(body) => body,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        if let Maybe::Present(receiver) = function.receiver {
            body = method::hold_body(receiver, body, sink, origin);
        }
        body = match CapabilityRef::new(self.host_ref()).place_body(function.endpoints, body, sink)
        {
            Maybe::Present(placed) => placed,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut fixpoint = match NativeRef::over(self.cx()).evidence(function) {
            Maybe::Present(evidence) => Some(evidence),
            Maybe::Absent(_) => None,
        };
        let staged = match function.recursion {
            Maybe::Present(scope) => self.cx().recursions.get(&scope).map_or(0, |recursion| {
                self.cx().parameters.read(recursion.uniform).len()
            }),
            Maybe::Absent(_) => 0,
        };
        for (position, parameter) in parameters.iter().enumerate().rev() {
            let Maybe::Present(binder) = self.cx().origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            // A linear tail's parameter is the linear lambda's: its body
            // reads the shadow in types and draws the one copy elsewhere.
            let id = if function.taking.of(parameter) == Taking::Linear {
                sink.arena.computation_linear_lambda(body)
            }
            else {
                sink.arena.computation_lambda(body)
            };
            sink.origins.record_computation(id, binder);
            sink.origins.record_binder(id, binder);
            body = id;
            if position == staged
                && let Some(evidence) = fixpoint.take()
            {
                body = self.close_fixpoint(function, body, evidence, sink, origin);
            }
        }
        // A tail of no parameter closes its fixpoint over its body: there is
        // no lambda for it to stand inside.
        if parameters.is_empty()
            && let Some(evidence) = fixpoint.take()
        {
            body = self.close_fixpoint(function, body, evidence, sink, origin);
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins
            .record_value(thunk, origin.inserted(Insertion::Thunk));

        Maybe::Present(Lowered::Function {
            signature: self.mint_signature(function, parameters, sink, origin),
            body: thunk,
        })
    }

    /// Close `body` by `function`'s fixpoint, carrying `evidence`, marked as
    /// inserted at the declaration form `origin` writes.
    ///
    /// # Specification
    /// - requires: `function` recurses and `body` is minted.
    /// - ensures: the fixpoint over `body` with `evidence`, its origin the
    ///   inserted fixpoint's and its binder the tile writing the function's own
    ///   name, which a type its identified fields read names it by.
    /// - provides: the one closing of a recursive tail, under its lambdas or
    ///   over its body alone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_function`].
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_parameterless_recursive_tail_binds_its_own_name_1499`
    #[spec(
        ensures: |ret| sink.origins.computation(ret) == Maybe::Present(origin.inserted(Insertion::Fixpoint))
            && matches!(sink.arena.computation(ret), Some(&gandr_core_term::Computation::Fixpoint { .. })),
    )]
    fn close_fixpoint(
        &self,
        function: &Function,
        body: ComputationId,
        evidence: gandr_kernel_term::FixpointEvidence,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let closed = sink.arena.computation_fixpoint(body, evidence);
        sink.origins
            .record_computation(closed, origin.inserted(Insertion::Fixpoint));
        if let Maybe::Present(scope) = function.recursion
            && let Some(recursion) = self.cx().recursions.get(&scope)
            && let Maybe::Present(named) = self.cx().origin_at(recursion.named)
        {
            sink.origins.record_binder(closed, named);
        }

        closed
    }

    /// Mint a function tail's declared type, `+U (A1 -> … -> An -> C)`.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's own, and every type position
    ///   has been classified, so every parameter a type names is recorded as
    ///   mentioned.
    /// - ensures: the declared type, as [`Self::mint_function`] states it, with
    ///   each parameter's arrow dependent exactly when a later parameter's type
    ///   or the result names it, and plain otherwise, each parameter of a
    ///   flattened model implicit at its component's type
    ///   (`ModelsRef::flattened_domains`), and each instance a label of the
    ///   result's row binds at the durable capability of the label's whole
    ///   interface, at the label's region binder; nothing is minted when a type
    ///   is unstated or did not lower.
    /// - provides: the signature half of [`Self::mint_function`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter a later type names beside one no type
    ///   names, each asserted as the exact arrow read back out of the arena.
    /// - witness: `gandr-surface-lowering::lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_row_label_is_an_instance_after_every_parameter_2271`
    #[spec(
        ensures: |ret| match function.result {
            | Maybe::Absent(_) => ret == Maybe::Absent(lowered::Absent::Unstated),
            | Maybe::Present(result) => match self.cx().comp_type_at(result) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    let missing =
                        parameters
                            .iter()
                            .find_map(|parameter| match parameter.declared {
                                | Maybe::Absent(stated::Absent::Instance) => None,
                                | Maybe::Absent(stated::Absent::Unstated) => Some(lowered::Absent::Unstated),
                                | Maybe::Present(written) => match self.cx().value_type_at(written) {
                                    | Maybe::Absent(reason) => Some(reason),
                                    | Maybe::Present(_) => None,
                                },
                            });
                    match missing {
                        | Some(reason) => ret == Maybe::Absent(reason),
                        | None if parameters.iter().any(|parameter| {
                            matches!(self.cx().origin_at(parameter.binder), Maybe::Absent(_))
                        }) =>
                        {
                            ret == Maybe::Absent(lowered::Absent::Unminted)
                        },
                        | None => {
                            matches!(ret, Maybe::Present(id) if sink.origins.value_type(id) == Maybe::Present(origin))
                                || (parameters.iter().any(|parameter| parameter.component.is_some())
                                    && ret == Maybe::Absent(lowered::Absent::Unminted))
                        },
                    }
                },
            },
        },
    )]
    fn mint_signature(
        &self,
        function: &Function,
        parameters: &[Parameter],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Maybe::Present(result) = function.result
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let mut declared = match self.cx().comp_type_at(result) {
            Maybe::Present(result) => result,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        if let Maybe::Present(receiver) = function.receiver {
            declared = match CapabilityRef::new(self.host_ref())
                .written_result(receiver, parameters, declared, sink, origin)
            {
                Maybe::Present(written) => written,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
        }
        for parameter in parameters {
            let written = match parameter.declared {
                Maybe::Present(written) => written,
                Maybe::Absent(stated::Absent::Instance) => continue,
                Maybe::Absent(stated::Absent::Unstated) => {
                    return Maybe::Absent(lowered::Absent::Unstated);
                },
            };
            if let Maybe::Absent(reason) = self.cx().value_type_at(written) {
                return Maybe::Absent(reason);
            }
        }
        // A flattened model implicit's parameters take their types from the
        // model type they share, minted once for the group.
        let mut flattened: BTreeMap<NodeIndex, Vec<ValueTypeId>> = BTreeMap::new();
        for (index, parameter) in parameters.iter().enumerate().rev() {
            let Maybe::Present(binder) = self.cx().origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let domain = match (parameter.declared, parameter.component) {
                (Maybe::Absent(stated::Absent::Instance), _) => {
                    self.mint_instance(parameter.binder, sink, origin)
                },
                (Maybe::Absent(stated::Absent::Unstated), _) => None,
                (Maybe::Present(written), Some(place)) => {
                    let domains = match flattened.entry(written) {
                        Entry::Occupied(held) => held.into_mut(),
                        Entry::Vacant(free) => {
                            match ModelsRef::new(self.host_ref())
                                .flattened_domains(written, sink, origin)
                            {
                                Maybe::Present(domains) => free.insert(domains),
                                Maybe::Absent(reason) => return Maybe::Absent(reason),
                            }
                        },
                    };
                    domains.get(usize::from(place)).copied()
                },
                (Maybe::Present(written), None) => match self.cx().value_type_at(written) {
                    Maybe::Present(domain) => Some(Parameter::shared_domain(
                        parameters.get(.. index).unwrap_or_default(),
                        parameter,
                        |named| bool::from(self.cx().scope.mentioned(named.frame)),
                        domain,
                        sink,
                        origin,
                    )),
                    Maybe::Absent(_) => None,
                },
            };
            let Some(domain) = domain
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = if function.taking.of(parameter) == Taking::Linear {
                // A linear parameter's arrow binds its shadow whatever the
                // result names, at the multiplicity one.
                let one = match multiplicity_one(sink, binder) {
                    Maybe::Present(one) => one,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let id = sink.arena.comp_type_linear_arrow(domain, one, declared);
                sink.origins.record_arrow(id, binder);
                id
            }
            else if bool::from(self.cx().scope.mentioned(parameter.frame)) {
                let id = sink.arena.comp_type_pi(domain, declared);
                sink.origins.record_arrow(id, binder);
                id
            }
            else {
                sink.arena.comp_type_arrow(domain, declared)
            };
            sink.origins.record_comp_type(id, binder);
            declared = id;
        }
        let id = sink.arena.value_type_thunk(declared);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(id)
    }

    /// Mint the type of the instance parameter whose binder tile is `binder`:
    /// the durable capability of its interface's whole signature at the
    /// region binder it lives at.
    ///
    /// # Specification
    /// - requires: every type a theory instance's row entry fixes is already
    ///   minted or absent.
    /// - ensures: `Cap {I} at r` at `origin` for the instance of `I` living at
    ///   the region binder `r`, `I` the theory at the sorts its row entry fixes
    ///   when its label names one ([`CapabilityRef::interface_signature`]);
    ///   none for a binder binding no instance, an interface the host does not
    ///   declare and no row entry read as a theory, or a fixed type that did
    ///   not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_signature`].
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::a_row_label_is_an_instance_after_every_parameter_2271`
    /// - witness: `gandr-surface-lowering::lower::capability::tests::a_row_names_a_theory_at_the_sorts_it_fixes_2844`
    #[spec(ensures: |ret| ret.is_none_or(|id| sink.origins.value_type(id) == Maybe::Present(origin)))]
    fn mint_instance(
        &self,
        binder: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Option<ValueTypeId>
    {
        let &(ref interface, region) = self.cx().instance_parameters.get(&binder)?;
        let signature = match self.cx().instance_theories.get(&binder) {
            Some(theory) => CapabilityRef::new(self.host_ref()).interface_signature(
                &capability::Interface::Theory(Arc::clone(theory)),
                capability::Standing::Read,
                sink,
                origin,
            ),
            None => sink.signature(interface, origin),
        };
        let Maybe::Present(signature) = signature
        else {
            return None;
        };
        let id = sink.arena.value_type_capability(
            gandr_core_term::effect::EffectRow::singleton(signature),
            gandr_core_term::effect::capability::CapabilityGrade::Durable,
            gandr_core_term::effect::capability::Region::Bound(region),
        );
        sink.origins.record_value_type(id, origin);

        Some(id)
    }

    /// Mint an interpolated string as `string.append` calls folded from the
    /// left.
    ///
    /// # Specification
    /// - requires: `segments` is a stretch of the segment store that
    ///   [`Self::interpolation`](crate::lower::Expressions::interpolation)
    ///   planned.
    /// - ensures: each text segment mints its literal and each operand reads
    ///   its own value; the first two segments are appended, and each later
    ///   segment is appended to the nested run of the call before it, so the
    ///   answer is the segments' text in written order. A string whose one
    ///   segment is an interpolation appends it to the empty string, so it
    ///   stands at `String` as any other string does.
    /// - fails: an operand that did not lower as a value leaves the string
    ///   unminted, with that operand's reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::interpolation`](crate::lower::Expressions::interpolation).
    /// - witness: `gandr-surface-lowering::lower::tests::an_interpolated_string_appends_its_segments_in_order`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    fn mint_interpolated(
        &self,
        append: gandr_core_term::primitive::Primitive,
        segments: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        use gandr_core_term::primitive::Arguments;
        let mut first = None;
        let mut called = None;
        for segment in self.cx().segments.read(segments) {
            let value = match *segment {
                TextSegment::Text(ref text) => {
                    let id = sink.arena.value_literal(Literal::Text(text.clone()));
                    sink.origins.record_value(id, origin);
                    id
                },
                TextSegment::Operand(node) => match self.cx().value_at(node) {
                    Maybe::Present(id) => id,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                },
            };
            let left = match (called, first) {
                (Some(previous), _) => {
                    sink.origins.record_computation(previous, origin);
                    let nested = sink.arena.value_nested(previous);
                    sink.origins
                        .record_value(nested, origin.inserted(Insertion::Nested));
                    nested
                },
                (None, Some(left)) => left,
                (None, None) => {
                    first = Some(value);
                    continue;
                },
            };
            called = Some(
                sink.arena
                    .computation_primitive(append, Arguments::Binary([left, value])),
            );
        }
        let id = match (called, first) {
            (Some(id), _) => id,
            (None, Some(lone)) => {
                let empty = sink
                    .arena
                    .value_literal(Literal::Text(StringLiteral::new(String::new())));
                sink.origins.record_value(empty, origin);
                sink.arena
                    .computation_primitive(append, Arguments::Binary([empty, lone]))
            },
            (None, None) => return Maybe::Absent(lowered::Absent::Unminted),
        };

        Maybe::Present(sink.computation(id, origin))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Resolve every attribute against the registry and file it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so an admitted payload already has
    ///   its core value.
    /// - ensures: every attribute of every declaration, refused or not, is
    ///   resolved against the registry and filed under the content identity of
    ///   the declaration form it decorates, in source order; an attribute
    ///   written twice for one declared name is refused wherever its two
    ///   spellings sit, and the earlier one is the one kept. A declaration's
    ///   lowering outcome does not gate its attributes: an expectation about a
    ///   refusal is read off the refused declaration, and an attribute's own
    ///   refusal competes with the declaration's other refusals by position. An
    ///   attribute decorating a top-level module is resolved alike and filed
    ///   under the module form's content identity, its refusal offered to the
    ///   module's first member. An `explicit_exits` attribute marks the slot it
    ///   decorates, or every member slot of the module it decorates, as asking
    ///   for written exits. The constants a `respects` or `entry` payload names
    ///   are filed beside its entry, as laws or as worlds.
    /// - provides: the attribute side table of the lowered module, and the
    ///   slots the `explicit-exits` lint reads as asked.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass. Every other refusal
    ///   is offered to the declaration that owns the attribute rather than
    ///   raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — attributes are drained and filed even for a refused
    ///   declaration, while a failing schema is retained as a declaration
    ///   refusal; an `explicit_exits` attribute on a module and on a
    ///   declaration asks within its form and nowhere else.
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `gandr-surface-lowering::lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's attributes; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.cx().collected.slots.len(),
        ensures: |ret| {
            self.cx().collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || (self.cx().collected.decorated.is_empty()
                        && self
                            .cx().collected
                            .slots
                            .iter()
                            .all(|slot| slot.attributes.is_empty())))
        },
    )]
    #[inline]
    pub fn attribute(
        &mut self,
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut slots = core::mem::take(&mut self.cx_mut().collected.slots);
        let decorated = core::mem::take(&mut self.cx_mut().collected.decorated);
        let outcome = self
            .attribute_slots(&mut slots, table, arena)
            .and_then(|()| self.attribute_modules(&decorated, &mut slots, table, arena));
        self.cx_mut().collected.slots = slots;

        outcome
    }

    /// Resolve and file the attributes of every decorated module in
    /// `decorated`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the decorated modules and the
    ///   slots taken out of the collection.
    /// - ensures: as [`Self::attribute`], for the modules' attributes; each
    ///   spends one step.
    /// - provides: the module walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decorated module of two members and an undecorated
    ///   declaration after it, the attribute reaching the members only; a
    ///   module's laws filed under the module; a refused attribute refusing the
    ///   first member alone.
    /// - witness: `gandr-surface-lowering::lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_respects_attribute_files_its_laws_under_the_module`
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_attribute_refusal_refuses_its_first_member_alone`
    #[spec(
        captures: before = (self.cx().fuel.remaining(), usize::from(table.attributed_count())),
        ensures: |ret| {
            self.cx().fuel.remaining() <= before.0
                && usize::from(table.attributed_count()) >= before.1
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
        },
    )]
    fn attribute_modules(
        &mut self,
        decorated: &[DecoratedModule<'source>],
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
        for module in decorated {
            seen.clear();
            for written in &module.attributes {
                self.cx_mut().fuel.spend()?;
                match self.shared().read_attribute(written, &mut seen, arena) {
                    Ok(Filing::Filed {
                        entry,
                        named,
                        members: _,
                        spelled,
                    }) => {
                        if entry.name() == RegisteredAttribute::EXPLICIT_EXITS {
                            self.cx_mut().asked.extend(
                                (usize::from(module.first) .. usize::from(module.end))
                                    .map(SlotIndex::from),
                            );
                        }
                        Exits::new(self.host()).ask_runs(
                            &entry,
                            (usize::from(module.first) .. usize::from(module.end))
                                .map(SlotIndex::from),
                        );
                        let key = self.shared().key_at(module.module.node);
                        let attribute = entry.name();
                        let at = entry.span();
                        table.file(key, entry);
                        table.file_named(key, attribute, named);
                        if let Some(spelled) = spelled {
                            table.file_spelled(key, at, spelled);
                        }
                    },
                    Ok(Filing::Unlowered) => {},
                    Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        if let Some(slot) = slots.get_mut(usize::from(module.first)) {
                            slot.refuse(written.at.node, refusal);
                        }
                    },
                }
            }
        }

        Ok(())
    }

    /// Resolve and file the attributes of every slot in `slots`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::attribute`].
    /// - provides: the slot walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each written attribute spends one step, successful
    ///   entries append under their declaration key, and schema errors do not
    ///   prevent other declarations from lowering.
    /// - witness: `gandr-surface-lowering::lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `gandr-surface-lowering::lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body resolves every slot's attributes; the capture counts them once"
        )
    )]
    #[spec(
        captures: before = (
            usize::from(self.cx().fuel.remaining()),
            slots.iter().fold(0_usize, |count, slot| {
                count.saturating_add(slot.attributes.len())
            }),
            usize::from(table.attributed_count()),
        ),
        ensures: |ret| {
            usize::from(self.cx().fuel.remaining()) <= before.0
                && usize::from(table.attributed_count()) >= before.2
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || usize::from(self.cx().fuel.remaining()) == before.0.saturating_sub(before.1))
        },
    )]
    fn attribute_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
        for (index, slot) in slots.iter_mut().enumerate() {
            seen.clear();
            for written in core::mem::take(&mut slot.attributes) {
                self.cx_mut().fuel.spend()?;
                match self.shared().read_attribute(&written, &mut seen, arena) {
                    Ok(Filing::Filed {
                        entry,
                        named,
                        members,
                        spelled,
                    }) => {
                        if entry.name() == RegisteredAttribute::EXPLICIT_EXITS {
                            let _first = self.cx_mut().asked.insert(SlotIndex::from(index));
                        }
                        Exits::new(self.host()).ask_runs(&entry, [SlotIndex::from(index)]);
                        let key = self.shared().key_at(written.decorates);
                        let attribute = entry.name();
                        let at = entry.span();
                        table.file(key, entry);
                        table.file_named(key, attribute, named);
                        if let Some(spelled) = spelled {
                            table.file_spelled(key, at, spelled);
                        }
                        if !members.is_empty() {
                            table.file_interface(key, members);
                        }
                    },
                    Ok(Filing::Unlowered) => {},
                    Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        slot.refuse(written.at.node, refusal);
                    },
                }
            }
        }

        Ok(())
    }

    /// Read every declaration's, every module's and every source's own
    /// documentation and check its links.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so every declaration form's key is
    ///   final.
    /// - ensures: every piece of documentation of every declaration, refused or
    ///   not, and of every module form, is read and filed under the content
    ///   identity of the form it documents, pieces in source order; each link
    ///   to a name the module neither declares nor recognises refuses its
    ///   declaration at the link, as a misspelt attribute does, and a module's
    ///   as [`Self::document_modules`] states. Each source's own documentation
    ///   is filed under the source, as [`Self::document_files`] states. Every
    ///   slot's documentation list and the module documentation are drained.
    /// - provides: the documentation tables of the lowered module, by form and
    ///   by source.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass; every other refusal
    ///   is offered to the declaration the documentation belongs to.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both spellings file one text under one key, a link to
    ///   a later declaration resolves, a link to a missing name refuses its
    ///   declaration at the link's span, a module's documentation is filed
    ///   under its own form, and a source's under the source.
    /// - witness: `gandr-surface-lowering::lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_s_documentation_is_filed_under_its_key_1135`
    /// - witness: `gandr-surface-lowering::lower::tests::a_source_s_documentation_is_filed_under_the_source_1365`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.cx().collected.slots.len(),
        ensures: |ret| {
            self.cx().collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || self.cx().collected.slots.iter().all(|slot| slot.docs.is_empty()))
        },
    )]
    #[inline]
    pub fn document(&mut self) -> Result<Filed<'source>, LoweringRefusal<'source>>
    {
        let mut filed = Filed::default();
        let mut slots = core::mem::take(&mut self.cx_mut().collected.slots);
        let modules = core::mem::take(&mut self.cx_mut().collected.module_docs);
        // Built on the first link the pass resolves, never for a unit whose
        // documentation links nothing.
        let names = OnceCell::new();
        let outcome = self
            .document_slots(&mut slots, &mut filed.forms, &names)
            .and_then(|()| self.document_modules(&modules, &mut slots, &mut filed.forms, &names))
            .and_then(|()| self.document_files(&mut slots, &mut filed.sources, &names));
        self.cx_mut().collected.slots = slots;

        outcome.map(|()| filed)
    }

    /// Read and file each source's own documentation, every `//!` run standing
    /// at a root, into `files`.
    ///
    /// # Specification
    /// - requires: as [`Self::document`], over the slots taken out of the
    ///   collection.
    /// - ensures: each run is filed under the source of the unit it stands in,
    ///   runs in source order, and spends one step; a run that does not read,
    ///   or a link to a name the module neither declares nor recognises,
    ///   refuses the source's first slot, as a module's documentation refuses
    ///   its first member. A source with no slot files its documentation and
    ///   has none to refuse. A `//!` run inside a form documents that form's
    ///   inside and is not read.
    /// - provides: the source walk of [`Self::document`].
    /// - fails: as [`Self::document`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::document`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sources' runs each filed under their own source,
    ///   two runs of one source joined, a `///` run at a root left alone, and a
    ///   link to a missing name refusing the source's first declaration at the
    ///   link.
    /// - witness: `gandr-surface-lowering::lower::tests::a_source_s_documentation_is_filed_under_the_source_1365`
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: self.cx().fuel.remaining() <= before,
    )]
    fn document_files(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        files: &mut BTreeMap<SourceIndex, Documentation<'source>>,
        names: &OnceCell<LinkNames<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let tree = self.cx().tree;
        for &root in tree.roots() {
            for child in tree.children(root) {
                let Some(node) = tree.node(child)
                else {
                    continue;
                };
                let inner = tree
                    .fragment(child)
                    .is_some_and(|written| <&str>::from(written).starts_with(INNER_DOC_LINE));
                if node.label() != NodeLabel::Doc || !inner {
                    continue;
                }
                self.cx_mut().fuel.spend()?;
                let unit = &self.cx().collected.unit;
                let source = unit.source_at(node.span().start());
                let first = slots.iter().position(|slot| {
                    [&slot.signature, &slot.definition]
                        .into_iter()
                        .find_map(|half| match *half {
                            Maybe::Present(half) => Some(half.declaration.span.start()),
                            Maybe::Absent(_) => None,
                        })
                        .is_some_and(|start| unit.source_at(start) == source)
                });
                let documentation = files.entry(source).or_default();
                let before = documentation.link_count();
                if let Err(refusal) = read_doc(self.cx().pbg, tree, child, documentation) {
                    if refusal.classify() == FailureClass::EngineFault {
                        return Err(refusal);
                    }
                    if let Some(slot) = first.and_then(|first| slots.get_mut(first)) {
                        slot.refuse(child, refusal);
                    }
                    continue;
                }
                self.shared().resolve_links(
                    documentation,
                    (before, names),
                    Container::TopLevel(source),
                    &mut |refusal| {
                        if let Some(slot) = first.and_then(|first| slots.get_mut(first)) {
                            slot.refuse(child, refusal);
                        }
                    },
                );
            }
        }

        Ok(())
    }

    /// Read and file the documentation of every module form, `docs`, into
    /// `filed`.
    ///
    /// # Specification
    /// - requires: as [`Self::document`], over the module documentation and the
    ///   slots taken out of the collection.
    /// - ensures: each piece is filed under the content identity of the module
    ///   form it documents, pieces in source order, and spends one step; a
    ///   piece that does not read, or a link to a name the module neither
    ///   declares nor recognises, refuses the module's first slot, a nested
    ///   module's included, as a module's refused attribute does. A module with
    ///   no slot files its documentation and has none to refuse.
    /// - provides: the module walk of [`Self::document`].
    /// - fails: as [`Self::document`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::document`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's, a decorated module's and a nested
    ///   module's documentation each filed under its own module, a member's
    ///   under its member, and a module's link to a missing name refusing its
    ///   first member at the link.
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_s_documentation_is_filed_under_its_key_1135`
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: self.cx().fuel.remaining() <= before,
    )]
    fn document_modules(
        &mut self,
        docs: &[WrittenDoc],
        slots: &mut [DeclarationSlot<'source>],
        filed: &mut BTreeMap<UnitKey, Documentation<'source>>,
        names: &OnceCell<LinkNames<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        // Each module by its form, read once for every piece of documentation.
        let modules: BTreeMap<NodeIndex, StructureIndex> = self
            .cx()
            .collected
            .structures
            .iter()
            .enumerate()
            .map(|(at, structure)| (structure.declared_by.node, StructureIndex::from(at)))
            .collect();
        for written in docs {
            self.cx_mut().fuel.spend()?;
            let module = modules.get(&written.documents).copied();
            let first = module.and_then(|module| self.shared().first_slot(module));
            let documentation = filed
                .entry(self.shared().key_at(written.documents))
                .or_default();
            let before = documentation.link_count();
            if let Err(refusal) = read_doc(
                self.cx().pbg,
                self.cx().tree,
                written.at.node,
                documentation,
            ) {
                if refusal.classify() == FailureClass::EngineFault {
                    return Err(refusal);
                }
                if let Some(slot) = first.and_then(|first| slots.get_mut(usize::from(first))) {
                    slot.refuse(written.at.node, refusal);
                }
                continue;
            }
            // A module's documentation reads its links inside the module.
            let container = module.map_or_else(
                || Container::TopLevel(self.cx().collected.unit.source_at(written.at.span.start())),
                Container::Module,
            );
            self.shared().resolve_links(
                documentation,
                (before, names),
                container,
                &mut |refusal| {
                    if let Some(slot) = first.and_then(|first| slots.get_mut(usize::from(first))) {
                        slot.refuse(written.at.node, refusal);
                    }
                },
            );
        }

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// The first slot the module `module` admitted, its nested modules'
    /// included, in source order.
    ///
    /// # Specification
    /// trivial.
    fn first_slot(
        &self,
        module: StructureIndex,
    ) -> Option<SlotIndex>
    {
        let mut structure = self.cx().collected.structures.get(usize::from(module))?;
        loop {
            match *structure.members.first()? {
                Member::Slot(slot) => return Some(slot),
                Member::Module(nested) => {
                    structure = self.cx().collected.structures.get(usize::from(nested))?;
                },
            }
        }
    }

    /// Check each link `documentation` writes from its `before`th on, read in
    /// `container`: offer a link that nothing answers to `refuse`, and keep
    /// the declaration a link names as its target. `names` holds the unit's
    /// names by spelling, built here on the first link of the pass, so a link
    /// costs ordered-map lookups and never a walk of the collection.
    ///
    /// # Specification
    /// - requires: `before` is at most the count of the links; `names`, when
    ///   built, was built from this collection.
    /// - ensures: each link from the `before`th on whose name names nothing the
    ///   module declares or recognises — a resolved path, a declaration, a
    ///   module or a constructor — is offered to `refuse` as
    ///   [`LoweringRefusal::UnresolvedDocLink`] at its span. Each other link
    ///   whose name [`Self::link_target`] answers keeps that declaration as its
    ///   target ([`Documentation::target`]), once per name. The links are
    ///   unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a link to a missing name is refused at the link, and
    ///   a link to a declaration, plain or by a module path, keeps it.
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_keeps_the_declaration_it_resolves_to_4963`
    #[spec(
        captures: written = documentation.links().len(),
        ensures: documentation.links().len() == written,
    )]
    fn resolve_links(
        &self,
        documentation: &mut Documentation<'source>,
        (before, names): (LinkCount, &OnceCell<LinkNames<'source>>),
        container: Container,
        refuse: &mut dyn FnMut(LoweringRefusal<'source>),
    )
    {
        let fresh = documentation.links_from(before).len();
        if fresh == 0 {
            return;
        }
        let names = names.get_or_init(|| LinkNames::of(&self.cx().collected));
        let mut kept: BTreeSet<SurfaceName<'source>> = documentation
            .targets()
            .iter()
            .map(LinkTarget::name)
            .collect();
        for at in 0 .. fresh {
            let Some(&link) = documentation.links_from(before).get(at)
            else {
                continue;
            };
            let name = link.name();
            let spelled: &str = name.as_ref();
            let path = NamePath::from(spelled.split('.').map(Segment::from).collect::<Vec<_>>());
            let answered = matches!(
                self.cx().recognition.resolve_path(&path),
                PathResolution::Complete(_)
            ) || names.slots.contains_key(&name)
                || names.modules.contains_key(&name)
                || names.constructors.contains(&name);
            if !answered {
                refuse(LoweringRefusal::UnresolvedDocLink {
                    span: link.span(),
                    name,
                });
                continue;
            }
            if kept.contains(&name) {
                continue;
            }
            if let Maybe::Present(constant) = self.link_target(name, container, names) {
                kept.insert(name);
                documentation.target(name, constant);
            }
        }
    }

    /// The declaration the linked name `name` names, read in `container`.
    ///
    /// A plain name is looked up in `container`, then in each container around
    /// it, then in any container of the unit. A dotted path reads its leading
    /// segments as nested modules, the first one found as a plain name is,
    /// and its last segment as a member of the innermost one.
    ///
    /// # Specification
    /// - requires: `names` was built from this collection.
    /// - ensures: the admission position of the slot found as above;
    ///   [`linked::Absent::Undeclared`] when no slot answers, as for a module,
    ///   a constructor or a built-in name.
    /// - provides: the target a documentation link keeps.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain link, a link by a module path, a link to a
    ///   module and a link to a constructor are asserted at their targets.
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_keeps_the_declaration_it_resolves_to_4963`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(_) => !self.cx().collected.by_name.is_empty(),
        Maybe::Absent(_) => true,
    })]
    fn link_target(
        &self,
        name: SurfaceName<'source>,
        container: Container,
        names: &LinkNames<'source>,
    ) -> Maybe<ConstantIndex, linked::Absent>
    {
        let collected = &self.cx().collected;
        let spelled: &'source str = SourceFragment::from(name).into();
        let around = || {
            core::iter::successors(Some(container), |&held| match held {
                Container::Module(module) => collected
                    .structures
                    .get(usize::from(module))
                    .map(|structure| structure.container),
                Container::TopLevel(_) => None,
            })
        };
        let slot = match spelled.rsplit_once('.') {
            None => around()
                .find_map(|held| collected.by_name.get(&(held, name)).copied())
                .or_else(|| names.slots.get(&name).copied()),
            Some((modules, last)) => {
                let mut segments = modules.split('.');
                let head = SurfaceName::from(segments.next().unwrap_or_default());
                let mut module = around()
                    .find_map(|held| collected.modules.get(&(held, head)).copied())
                    .or_else(|| names.modules.get(&head).copied());
                for segment in segments {
                    module = module.and_then(|held| {
                        collected
                            .modules
                            .get(&(Container::Module(held), SurfaceName::from(segment)))
                            .copied()
                    });
                }
                module.and_then(|held| {
                    collected
                        .by_name
                        .get(&(Container::Module(held), SurfaceName::from(last)))
                        .copied()
                })
            },
        };
        slot.map_or(Maybe::Absent(linked::Absent::Undeclared), |slot| {
            Maybe::Present(ConstantIndex::from(usize::from(slot)))
        })
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Read and file the documentation of every slot in `slots` into `filed`.
    ///
    /// # Specification
    /// - requires: as [`Self::document`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::document`], for the slots' documentation; each
    ///   piece spends one step.
    /// - provides: the slot walk of [`Self::document`].
    /// - fails: as [`Self::document`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::document`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::document`], and a link to a module, its
    ///   member and a constructor, each resolved.
    /// - witness: `gandr-surface-lowering::lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    /// - witness: `gandr-surface-lowering::lower::tests::a_link_resolves_to_a_module_its_member_or_a_constructor`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.cx().fuel.remaining(),
        ensures: |ret| self.cx().fuel.remaining() <= before
            && (ret.is_err() || slots.iter().all(|slot| slot.docs.is_empty())),
    )]
    fn document_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        filed: &mut BTreeMap<UnitKey, Documentation<'source>>,
        names: &OnceCell<LinkNames<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for slot in slots.iter_mut() {
            for written in core::mem::take(&mut slot.docs) {
                self.cx_mut().fuel.spend()?;
                let documentation = filed
                    .entry(self.shared().key_at(written.documents))
                    .or_default();
                let before = documentation.link_count();
                if let Err(refusal) = read_doc(
                    self.cx().pbg,
                    self.cx().tree,
                    written.at.node,
                    documentation,
                ) {
                    if refusal.classify() == FailureClass::EngineFault {
                        return Err(refusal);
                    }
                    slot.refuse(written.at.node, refusal);
                    continue;
                }
                let container = slot.container;
                self.shared().resolve_links(
                    documentation,
                    (before, names),
                    container,
                    &mut |refusal| {
                        slot.refuse(written.at.node, refusal);
                    },
                );
            }
        }

        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Read one written attribute into an entry, or into the refusal it earns.
    ///
    /// # Specification
    /// - requires: `seen` holds the attributes already filed for this declared
    ///   name, with their spans.
    /// - ensures: a registered name whose payload its schema admits yields an
    ///   entry carrying the payload's already-minted value, and joins `seen`; a
    ///   payload whose form is not a value at all is refused before its schema
    ///   is consulted, because being no value is a different fact from being
    ///   the wrong one; nothing is filed for a payload the mint sweep left
    ///   unlowered, which is the case of a payload that itself refused; a text
    ///   where a marker-or-option schema stands is admitted only when it spells
    ///   the option, and is ill-typed as another text otherwise; a bare word
    ///   where a word schema stands is admitted only when it spells one of the
    ///   schema's words, filed with no value, and is ill-typed as another word
    ///   otherwise; a word or another value where the spelled schema stands, or
    ///   a named payload, is filed with no value and its spelling, every run of
    ///   layout one space and none just inside a parenthesis, a named one `name
    ///   = value`; a named payload is ill-typed where any other schema stands;
    ///   a `respects` or `entry` payload is admitted only when it names
    ///   declarations, an `identity` payload only when it names two or three,
    ///   which the filing carries, and a `deprecated` record only when its
    ///   fields are texts among those its schema names, and each is ill-typed
    ///   as another value otherwise.
    /// - provides: the per-attribute half of the attribute pass.
    /// - fails: yields the unknown-attribute refusal with its bounded
    ///   suggestion, the duplicate refusal naming the first spelling for a name
    ///   other than `traces` written again, the non-value-payload refusal, the
    ///   missing-payload refusal, or the ill-typed-payload refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The attribute's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed entry adds exactly one recognized name and
    ///   keeps its schema, payload and span; duplicate, unknown and ill-typed
    ///   attributes leave the per-declaration seen list unchanged.
    /// - witness: `gandr-surface-lowering::lower::tests::an_attribute_written_twice_for_one_name_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
    /// - witness: `gandr-surface-lowering::lower::tests::a_payload_of_the_wrong_form_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_form_payload_is_read_as_one_of_its_words`
    /// - witness: `gandr-surface-lowering::lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_spelled_payload_is_read_back_where_it_was_filed`
    /// - witness: `gandr-surface-lowering::lower::tests::a_named_payload_is_spelled_with_its_name_2077`
    /// - witness: `gandr-surface-lowering::lower::tests::traces_is_written_once_per_channel_3338`
    /// - witness: `gandr-surface-lowering::tests::modules::a_sealed_atom_reads_the_identity_its_type_member_states`
    #[spec(
        captures: before = seen.len(),
        ensures: |ret| match ret.as_ref() {
            | Ok(&Filing::Filed { ref entry, ref named, ref members, ref spelled }) => {
                seen.len() == before.saturating_add(1_usize)
                    && seen.last() == Some(&(entry.name(), written.span))
                    && entry.span() == written.span
                    && AttributeRegistry::lookup(written.name)
                        == Maybe::Present((entry.name(), entry.schema()))
                    && match (written.payload, entry.payload()) {
                        | (Payload::Unwritten, Maybe::Absent(payload::Absent::Marker)) => true,
                        | (Payload::Written(_), Maybe::Absent(payload::Absent::Word)) => {
                            matches!(entry.schema(), AttributeSchema::Word(_))
                        },
                        | (Payload::Written(_), Maybe::Absent(payload::Absent::Spelled)) => {
                            entry.schema() == AttributeSchema::Spelled
                        },
                        | (Payload::Written(placed), Maybe::Present(value)) => {
                            self.cx().value_at(placed.node) == Maybe::Present(value)
                        },
                        | _ => false,
                    }
                    && named.is_empty() == (entry.schema() != AttributeSchema::Names)
                    && members.is_empty() == (entry.schema() != AttributeSchema::Interface)
                    && (members.is_empty() || (2_usize ..= 3_usize).contains(&members.len()))
                    && spelled.is_some() == matches!(entry.schema(), AttributeSchema::Spelled | AttributeSchema::Word(_))
            },
            | Ok(&Filing::Unlowered) => {
                seen.len() == before
                    && matches!(written.payload, Payload::Written(placed) if matches!(self.cx().value_at(placed.node), Maybe::Absent(_)))
            },
            | Err(_) => seen.len() == before,
        },
    )]
    fn read_attribute(
        &self,
        written: &WrittenAttribute<'source>,
        seen: &mut Vec<(RegisteredAttribute, ByteSpan)>,
        arena: &CoreArena,
    ) -> Result<Filing, LoweringRefusal<'source>>
    {
        let Maybe::Present((name, schema)) = AttributeRegistry::lookup(written.name)
        else {
            return Err(LoweringRefusal::UnknownAttribute {
                span: written.span,
                name: written.name,
                suggestion: AttributeRegistry::suggestion(written.name),
            });
        };
        // `traces` states one channel an entry, so it alone is written again.
        if let Some(&(_held, first)) = seen
            .iter()
            .find(|&&(held, _first)| held == name && name != RegisteredAttribute::TRACES)
        {
            return Err(LoweringRefusal::DuplicateAttribute {
                span: written.span,
                name: written.name,
                first,
            });
        }
        let form = match (
            schema,
            self.payload_form_of(written, name, schema)?,
            written.payload,
        ) {
            (AttributeSchema::MarkerOr(option), PayloadForm::Text, Payload::Written(placed))
                if !matches!(
                    parse_literal(Former::Text, self.cx().text_at(placed)),
                    Maybe::Present(Literal::Text(ref text)) if text.as_ref() == option
                ) =>
            {
                PayloadForm::OtherText
            },
            (AttributeSchema::Word(words), PayloadForm::Word, Payload::Written(placed))
                if !words.contains(&self.cx().text_at(placed).as_ref()) =>
            {
                PayloadForm::OtherWord
            },
            (_, form, _) => form,
        };
        match payload_verdict(schema, form) {
            PayloadVerdict::Admitted => {},
            PayloadVerdict::Missing => {
                return Err(LoweringRefusal::MissingPayload {
                    span: written.span,
                    name,
                    expected: schema,
                });
            },
            PayloadVerdict::IllTyped => {
                let span = match written.payload {
                    Payload::Written(payload) => written
                        .key
                        .map_or(payload.span, |key| key.span.join(payload.span)),
                    Payload::Unwritten => written.span,
                };
                return Err(LoweringRefusal::IllTypedPayload {
                    span,
                    name,
                    expected: schema,
                    written: form,
                });
            },
        }
        let mut spelled = None;
        let (value, named, members) = match written.payload {
            Payload::Unwritten => (
                Maybe::Absent(payload::Absent::Marker),
                Vec::new(),
                Vec::new(),
            ),
            Payload::Written(placed) if matches!(schema, AttributeSchema::Word(_)) => {
                // The word as written. A `builtin` mark is read back by its
                // word.
                spelled = Some(String::from(self.cx().text_at(placed).as_ref()));
                (Maybe::Absent(payload::Absent::Word), Vec::new(), Vec::new())
            },
            Payload::Written(placed) if schema == AttributeSchema::Spelled => {
                // The payload as written, its layout one space and none just
                // inside a parenthesis, so a form written across lines reads
                // as one; a named payload is spelled `name = value`.
                let mut spelling = String::new();
                let key = written.key.map(|key| self.cx().text_at(key));
                let value = self.cx().text_at(placed);
                let words = key
                    .iter()
                    .flat_map(|key| key.as_ref().split_whitespace().chain(["="]))
                    .chain(value.as_ref().split_whitespace());
                for word in words {
                    if !spelling.is_empty() && !spelling.ends_with('(') && !word.starts_with(')') {
                        spelling.push(' ');
                    }
                    spelling.push_str(word);
                }
                spelled = Some(spelling);
                (
                    Maybe::Absent(payload::Absent::Spelled),
                    Vec::new(),
                    Vec::new(),
                )
            },
            Payload::Written(placed) => {
                let Maybe::Present(value) = self.cx().value_at(placed.node)
                else {
                    return Ok(Filing::Unlowered);
                };
                let read = match schema {
                    AttributeSchema::Names => match names(arena, value) {
                        Maybe::Present(named) => Maybe::Present((named, Vec::new())),
                        Maybe::Absent(absent) => Maybe::Absent(absent),
                    },
                    AttributeSchema::Interface => match members(arena, value) {
                        Maybe::Present(members) => Maybe::Present((Vec::new(), members)),
                        Maybe::Absent(absent) => Maybe::Absent(absent),
                    },
                    AttributeSchema::MarkerOrRecord(_) => match deprecation(arena, value) {
                        Maybe::Present(_) => Maybe::Present((Vec::new(), Vec::new())),
                        Maybe::Absent(absent) => Maybe::Absent(absent),
                    },
                    AttributeSchema::Texts => match texts(arena, value) {
                        Maybe::Present(_) => Maybe::Present((Vec::new(), Vec::new())),
                        Maybe::Absent(texts::Absent::Untexted) => {
                            return Err(LoweringRefusal::IllTypedPayload {
                                span: placed.span,
                                name,
                                expected: schema,
                                written: form,
                            });
                        },
                    },
                    AttributeSchema::Marker
                    | AttributeSchema::Integer
                    | AttributeSchema::Text
                    | AttributeSchema::MarkerOr(_)
                    | AttributeSchema::Word(_)
                    | AttributeSchema::Spelled => Maybe::Present((Vec::new(), Vec::new())),
                };
                let Maybe::Present((named, members)) = read
                else {
                    return Err(LoweringRefusal::IllTypedPayload {
                        span: placed.span,
                        name,
                        expected: schema,
                        written: form,
                    });
                };
                (Maybe::Present(value), named, members)
            },
        };
        seen.push((name, written.span));

        Ok(Filing::Filed {
            entry: AttributeEntry::new(name, schema, value, written.span),
            named,
            members,
            spelled,
        })
    }

    /// The form an attribute's payload was written in.
    ///
    /// # Specification
    /// - requires: `name` is the registered name `written` resolved to.
    /// - ensures: the absent form for no payload, the named form for a payload
    ///   written with a name, and the payload form of the payload's former
    ///   otherwise.
    /// - provides: the syntactic half of the payload verdict.
    /// - fails: yields the non-value-payload refusal for a payload that cannot
    ///   stand as a value, unless `schema` reads it as its spelling, and
    ///   [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::NonValuePayload`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an absent payload is distinguished from a non-value
    ///   form and from an admitted value of the wrong schema-specific shape.
    /// - witness: `gandr-surface-lowering::lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
    /// - witness: `gandr-surface-lowering::lower::tests::a_non_value_payload_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_payload_of_the_wrong_form_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_named_payload_is_spelled_with_its_name_2077`
    #[spec(
        ensures: |ret| {
            ret == match written.payload {
                | Payload::Written(_) if written.key.is_some() => Ok(PayloadForm::Named),
                | Payload::Unwritten => Ok(PayloadForm::Absent),
                | Payload::Written(placed) => match self.payload_former(placed) {
                    | Err(refusal) => Err(refusal),
                    | Ok((Shape::Form { former, .. }, ValueForm(true))) => Ok(payload_form(former)),
                    | Ok((Shape::Form { former, .. }, _)) if schema == AttributeSchema::Spelled => {
                        Ok(payload_form(former))
                    },
                    | Ok((Shape::Form { name: form, .. }, ValueForm(false))) => {
                        Err(LoweringRefusal::NonValuePayload {
                            span: placed.span,
                            name,
                            form,
                        })
                    },
                    | Ok(_) => Ok(PayloadForm::OtherValue),
                },
            }
        },
    )]
    fn payload_form_of(
        &self,
        written: &WrittenAttribute<'source>,
        name: RegisteredAttribute,
        schema: AttributeSchema,
    ) -> Result<PayloadForm, LoweringRefusal<'source>>
    {
        let Payload::Written(placed) = written.payload
        else {
            return Ok(PayloadForm::Absent);
        };
        if written.key.is_some() {
            return Ok(PayloadForm::Named);
        }
        let (shape, value) = self.payload_former(placed)?;
        let Shape::Form { name: form, former } = shape
        else {
            return Ok(PayloadForm::OtherValue);
        };
        if !value.0 && schema != AttributeSchema::Spelled {
            return Err(LoweringRefusal::NonValuePayload {
                span: placed.span,
                name,
                form,
            });
        }

        Ok(payload_form(former))
    }

    /// The key of the node at `position` in its unit: the source holding it,
    /// then its top-level form's digest and its rank there.
    ///
    /// # Specification
    /// - requires: positions are interpreted in this source tree.
    /// - ensures: a node with a tree key yields it beside the source of the
    ///   unit whose text holds the node; any other position yields the all-zero
    ///   key in the first source.
    /// - provides: declaration keys for attribute and documentation filing,
    ///   apart for one form written in two sources of the unit (#596).
    /// - fails: the fallback does not distinguish a keyless position from an
    ///   equal key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — filed attributes use the decorated declaration's key,
    ///   including declarations already refused for an unrelated source error;
    ///   one attributed form in two members of a component settles each under
    ///   its own expectation.
    /// - witness: `gandr-surface-lowering::lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::tests::namespace::one_form_in_two_sources_files_its_attributes_apart_596`
    #[spec(
        ensures: |ret| {
            ret == match (self.cx().tree.key(position), self.cx().tree.node(position)) {
                (Some(key), Some(node)) => {
                    UnitKey::new(self.cx().collected.unit.source_at(node.span().start()), key)
                },
                _ => UnitKey::new(
                    SourceIndex::default(),
                    NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default()),
                ),
            }
        },
    )]
    fn key_at(
        &self,
        position: NodeIndex,
    ) -> UnitKey
    {
        match (self.cx().tree.key(position), self.cx().tree.node(position)) {
            (Some(key), Some(node)) => {
                UnitKey::new(self.cx().collected.unit.source_at(node.span().start()), key)
            },
            _ => UnitKey::new(
                SourceIndex::default(),
                NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default()),
            ),
        }
    }

    /// The key of the declaration form `slot`'s refusal was raised at while it
    /// was collected, when no half of the slot is written there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key at the refusing node when the slot's refusal is a
    ///   duplicate signature or definition, or was raised at a `def` form no
    ///   half of the slot is written at — a form refused before it wrote one;
    ///   the key of a module form whose own held slot writes no half, when the
    ///   refusal was raised inside it — a module refused at its header, not a
    ///   member or a signature component; absent otherwise.
    /// - provides: the key the attributes of a form refused at collection are
    ///   filed under, which the corpus reads its expectation off (#1798), and
    ///   the key a table holds a module refused at its header by (#2183).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module defining one member twice keys its second
    ///   definition, which no half reaches, and a name written once keys none;
    ///   a module whose header names a sort its theory lacks keys its own form;
    ///   the corpus's settlement of a form refused at collection exercises the
    ///   remaining arm.
    /// - witness: `gandr-surface-lowering::lower::tests::a_duplicate_definition_is_keyed_at_its_form`
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_refused_at_its_header_is_keyed_at_its_form_2183`
    #[spec(ensures: |ret| ret == match slot.refusal {
        Maybe::Present((at, LoweringRefusal::DuplicateDefinition { .. } | LoweringRefusal::DuplicateSignature { .. })) => Maybe::Present(self.key_at(at)),
        Maybe::Present((at, _)) => self.form_refused_at(slot, at),
        Maybe::Absent(_) => Maybe::Absent(declaration_half::Absent::Unwritten),
    })]
    fn refused_form_key(
        &self,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<UnitKey, declaration_half::Absent>
    {
        match slot.refusal {
            Maybe::Present((
                at,
                LoweringRefusal::DuplicateDefinition { .. }
                | LoweringRefusal::DuplicateSignature { .. },
            )) => Maybe::Present(self.key_at(at)),
            Maybe::Present((at, _)) => self.form_refused_at(slot, at),
            Maybe::Absent(_) => Maybe::Absent(declaration_half::Absent::Unwritten),
        }
    }

    /// The key of the form refused at `at`: a `def` form of `slot` that no
    /// half of it is written at, refused while it was collected, or a module
    /// form whose own held slot writes no half at all — a module refused at
    /// its header — when `at` stands inside it.
    ///
    /// # Specification
    /// - requires: `at` is the node `slot`'s refusal was raised at.
    /// - ensures: as [`Self::refused_form_key`] for a refusal other than a
    ///   duplicate.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the halves and the introducing form are read
    ///   through the tree, which a predicate would walk again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::refused_form_key`].
    /// - witness: `gandr-surface-lowering::lower::tests::a_module_refused_at_its_header_is_keyed_at_its_form_2183`
    fn form_refused_at(
        &self,
        slot: &DeclarationSlot<'source>,
        at: NodeIndex,
    ) -> Maybe<UnitKey, declaration_half::Absent>
    {
        let halved = [slot.signature, slot.definition]
            .into_iter()
            .any(|half| matches!(half, Maybe::Present(half) if half.declaration.node == at));
        let form = self.cx().tree.node(at).is_some_and(|node| {
            matches!(
                shape_of(self.cx().pbg, node),
                Ok(Shape::Form {
                    former: Former::Declaration,
                    ..
                })
            )
        });
        if form && !halved {
            return Maybe::Present(self.key_at(at));
        }
        let module = self
            .cx()
            .tree
            .node(slot.introduced_by.node)
            .is_some_and(|node| {
                matches!(
                    shape_of(self.cx().pbg, node),
                    Ok(Shape::Form {
                        former: Former::Module,
                        ..
                    })
                )
            });
        // A component standing for itself is introduced by its own name tile:
        // only a module's own held slot is introduced by a form wider than its
        // name.
        let unhalved = module
            && slot.role == Role::Held
            && slot.introduced_by.node != slot.named.node
            && matches!(
                (slot.signature, slot.definition),
                (Maybe::Absent(_), Maybe::Absent(_))
            );
        let introducing = slot.introduced_by.span;
        let inside = self.cx().tree.node(at).is_some_and(|node| {
            introducing.start() <= node.span().start() && node.span().end() <= introducing.end()
        });
        if unhalved && inside {
            Maybe::Present(self.key_at(slot.introduced_by.node))
        }
        else {
            Maybe::Absent(declaration_half::Absent::Unwritten)
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Mint each callable operation's type and body from its plan.
    ///
    /// # Specification
    /// - requires: the collection planned the operations.
    /// - ensures: one minted type and body per planned operation whose slot
    ///   holds no refusal, every node with the operation's origin.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a planned operation lowers to a completed declaration
    ///   the checker accepts and the machine runs.
    /// - witness: `gandr-surface-lowering::tests::operation::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
    /// - witness: `gandr-surface-lowering::tests::operation::a_call_reaches_the_operation_before_a_builtin_of_its_name`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body mints every planned operation once; the check looks up each minted slot once"
        )
    )]
    #[spec(ensures: self.cx().operated.keys().all(|slot| self.cx().collected.operations.contains_key(slot)))]
    fn mint_operations(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let cx = self.cx_mut();
        for (&slot, plan) in cx
            .collected
            .operations
            .range(SlotIndex::from(cx.current.slots) ..)
        {
            let Some(entry) = cx.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let origin = Origin::new(entry.named.node, entry.named.span);
            let minted = crate::operation::mint_operation(plan, sink.arena, sink.origins, origin);
            let _first = cx.operated.insert(slot, minted);
        }
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// Assemble one declaration per slot from `from` on, in admission order:
    /// every slot's for a lowering finished whole, and those past a closure's
    /// for one resumed after it, whose declarations the closure's module
    /// shares.
    ///
    /// # Specification
    /// - requires: the classification, the mint sweep and the attribute pass
    ///   have all run.
    /// - ensures: a slot holding a refusal yields the refused outcome; a slot
    ///   whose signature and definition both lowered yields the completed
    ///   outcome — a witness's definition being the member it re-states; a
    ///   signature alone yields the uncompleted outcome, which is the
    ///   obligation this module owes; a definition alone yields the bodiless
    ///   outcome. A held slot holding no refusal yields nothing, and neither
    ///   does a witness whose member refused: there is no member to state a
    ///   second type for. Each declaration keeps its container, its role and
    ///   where its name tile is written, and takes its own origin token, handed
    ///   out in admission order.
    /// - provides: the declaration list a checker drives.
    /// - fails: never — a slot with neither half lowered and no refusal
    ///   contributes no declaration, which the classification makes unreachable
    ///   for every slot but a held one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completed, one-sided and refused declarations retain
    ///   their own source metadata and appear in admission order; skipped
    ///   unminted slots do not fabricate declaration origins or change constant
    ///   coordinates.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `gandr-surface-lowering::lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `gandr-surface-lowering::tests::modules::module_members_admit_in_source_order`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body assembles a row from every slot once; the check rebuilds each row once and compares it"
        )
    )]
    #[spec(
        captures: before = usize::from(origins.declaration_count()),
        ensures: |ret| {
            usize::from(origins.declaration_count()) == before.saturating_add(ret.len())
                && ret
                    .iter()
                    .map(|row| {
                        (
                            row.name(),
                            row.container(),
                            row.role(),
                            row.constant(),
                            row.span(),
                            row.named(),
                            row.signature(),
                            row.definition(),
                            row.refused_form(),
                            row.introduced(),
                            row.outcome(),
                            origins.declaration(row.origin()),
                        )
                    })
                    .eq(self.cx().collected.slots.iter().enumerate().skip(usize::from(from)).filter_map(
                        |(position, slot)| match self.outcome(SlotIndex::from(position), slot) {
                            | Maybe::Absent(_) => None,
                            | Maybe::Present(outcome) => Some((
                                slot.name,
                                slot.container,
                                slot.role,
                                slot.constant,
                                slot.introduced_by.span,
                                slot.named.span,
                                slot.signature
                                    .map(|half| self.key_at(half.declaration.node)),
                                slot.definition
                                    .map(|half| self.key_at(half.declaration.node)),
                                self.refused_form_key(slot),
                                self.key_at(slot.introduced_by.node),
                                outcome,
                                Maybe::Present(Origin::new(
                                    slot.introduced_by.node,
                                    slot.introduced_by.span,
                                )),
                            )),
                        },
                    ))
        },
    )]
    #[inline]
    pub fn assemble(
        &self,
        origins: &mut OriginTable,
        from: SlotIndex,
    ) -> Vec<LoweredDeclaration<'source>>
    {
        let mut declarations = Vec::with_capacity(
            self.cx()
                .collected
                .slots
                .len()
                .saturating_sub(usize::from(from)),
        );
        for (position, slot) in self
            .cx()
            .collected
            .slots
            .iter()
            .enumerate()
            .skip(usize::from(from))
        {
            let Maybe::Present(outcome) = self.outcome(SlotIndex::from(position), slot)
            else {
                continue;
            };
            let introduced = slot.introduced_by;
            let origin = origins.record_declaration(Origin::new(introduced.node, introduced.span));
            declarations.push(LoweredDeclaration::from(DeclarationParts {
                name: slot.name,
                container: slot.container,
                role: slot.role,
                constant: slot.constant,
                span: introduced.span,
                named: slot.named.span,
                origin,
                signature: slot
                    .signature
                    .map(|half| self.key_at(half.declaration.node)),
                definition: slot
                    .definition
                    .map(|half| self.key_at(half.declaration.node)),
                refused_form: self.refused_form_key(slot),
                introduced: self.key_at(introduced.node),
                halves: Halves {
                    signature: slot.signature.map(half_at),
                    definition: slot.definition.map(half_at),
                },
                outcome,
                inertness: self.inertness(SlotIndex::from(position)),
                visibility: self
                    .cx()
                    .collected
                    .slot_visibility(SlotIndex::from(position)),
            }));
        }

        declarations
    }

    /// What the slot at `position` amounts to in the lowered module.
    ///
    /// # Specification
    /// - requires: the slot and its member coordinates are interpreted in this
    ///   lowering run, and the applications are minted.
    /// - ensures: a slot of a functor's template is its own refusal when
    ///   [`Self::own_outcome`] refuses it, so a refusal inside a functor is
    ///   reported once, where it was written, and templated otherwise; a slot
    ///   of an application is the declaration its renaming minted, unminted
    ///   when its template refused or its argument's type did not lower; a
    ///   path's function or round trip is the declaration
    ///   [`Self::mint_paths`](crate::lower::Expressions::mint_paths) minted for
    ///   it; any other module's own slot is [`Self::own_outcome`], except that
    ///   one [`Self::own_outcome`] leaves absent is refused by the expectation
    ///   its type member states unread, when it states one, and otherwise,
    ///   while it holds a half that lowers to a core term — any but a top-level
    ///   `oper`'s, the prelude's `Eq.generic`'s ([`Role::Generic`]), which
    ///   names the derivation, or a witness of a member refused where it was
    ///   written — is refused [`LoweringRefusal::Unminted`] at the declaration,
    ///   by its name; and a witness refused as the member it represents is,
    ///   yields nothing, so the member's refusal is reported once.
    /// - provides: the per-slot row [`Self::assemble`] files, so a declaration
    ///   the lowering collected either lowers or is refused by name, never
    ///   dropped from the module.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a functor's body yields no declaration and each of
    ///   two applications yields its own; a function whose two halves the mint
    ///   left unminted, with no refusal filed, is refused by name rather than
    ///   dropped silently; a type member's expectation states its refusal and
    ///   is refused when the member yields nothing.
    /// - witness: `gandr-surface-lowering::tests::modules::functors::a_functor_body_never_reaches_the_kernel`
    /// - witness: `gandr-surface-lowering::tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    /// - witness: `gandr-surface-lowering::tests::modules::functors::two_applications_mint_distinct_atoms`
    /// - witness: `gandr-surface-lowering::lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
    /// - witness: `gandr-surface-lowering::tests::modules::a_component_check_carries_its_members_expectation`
    #[spec(
        ensures: |ret| match self.cx().collected.stratum_of(slot.container) {
            | Stratum::Module if let Some(&pathed) = self.cx().pathed.get(&position) => ret == Maybe::Present(pathed),
            | Stratum::Module => match self.own_outcome(position, slot) {
                | Maybe::Absent(_) if let Some(&refusal) = self.cx().collected.unread_expectations.get(&position) => ret == Maybe::Present(DeclarationOutcome::Refused(refusal)),
                | Maybe::Absent(_) if self.lowers_a_half(slot) == Owed::Owed => ret == Maybe::Present(DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                    span: slot.introduced_by.span,
                    name: slot.name,
                })),
                | Maybe::Present(DeclarationOutcome::Refused(refusal)) if self.represented_refusal(position) == Some(refusal) => ret == Maybe::Absent(lowered::Absent::Unminted),
                | own => ret == own,
            },
            | Stratum::Functor(_) | Stratum::Parameter(_) => match self.own_outcome(position, slot) {
                | Maybe::Present(DeclarationOutcome::Refused(refusal)) => ret == Maybe::Present(DeclarationOutcome::Refused(refusal)),
                | Maybe::Absent(_) if let Some(&refusal) = self.cx().collected.unread_expectations.get(&position) => ret == Maybe::Present(DeclarationOutcome::Refused(refusal)),
                | _ => ret == Maybe::Absent(lowered::Absent::Templated),
            },
            | Stratum::Instance(_) => ret == self.cx().instantiated.get(&position).copied().map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
        },
    )]
    #[inline]
    pub fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        match self.cx().collected.stratum_of(slot.container) {
            Stratum::Module if let Some(&pathed) = self.cx().pathed.get(&position) => {
                Maybe::Present(pathed)
            },
            Stratum::Module => match self.own_outcome(position, slot) {
                Maybe::Absent(reason) => {
                    if let Some(&refusal) = self.cx().collected.unread_expectations.get(&position) {
                        return Maybe::Present(DeclarationOutcome::Refused(refusal));
                    }
                    match self.lowers_a_half(slot) {
                        Owed::Owed => {
                            Maybe::Present(DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                                span: slot.introduced_by.span,
                                name: slot.name,
                            }))
                        },
                        Owed::Nothing => Maybe::Absent(reason),
                    }
                },
                Maybe::Present(DeclarationOutcome::Refused(refusal))
                    if self.represented_refusal(position) == Some(refusal) =>
                {
                    Maybe::Absent(lowered::Absent::Unminted)
                },
                Maybe::Present(outcome) => Maybe::Present(outcome),
            },
            Stratum::Functor(_) | Stratum::Parameter(_) => match self.own_outcome(position, slot) {
                Maybe::Present(DeclarationOutcome::Refused(refusal)) => {
                    Maybe::Present(DeclarationOutcome::Refused(refusal))
                },
                Maybe::Absent(_) => match self.cx().collected.unread_expectations.get(&position) {
                    Some(&refusal) => Maybe::Present(DeclarationOutcome::Refused(refusal)),
                    None => Maybe::Absent(lowered::Absent::Templated),
                },
                Maybe::Present(_) => Maybe::Absent(lowered::Absent::Templated),
            },
            Stratum::Instance(_) => self
                .cx()
                .instantiated
                .get(&position)
                .copied()
                .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
        }
    }

    /// The refusal of the type member the witness at `position` checks, when
    /// it is a transparent component's witness and that member is refused;
    /// the atom an opaque ascription seals carries its member's refusal on to
    /// the declarations that read it, so it keeps it.
    ///
    /// # Specification
    /// trivial.
    fn represented_refusal(
        &self,
        position: SlotIndex,
    ) -> Option<LoweringRefusal<'source>>
    {
        if self.cx().collected.slots.get(usize::from(position))?.role != Role::Witness {
            return None;
        }
        let held = match self.cx().collected.abstracts.get(&position)?.representation {
            Maybe::Present(represented) => represented.held,
            Maybe::Absent(_) => return None,
        };
        match self.cx().collected.slots.get(usize::from(held))?.refusal {
            Maybe::Present((_at, refusal)) => Some(refusal),
            Maybe::Absent(_) => None,
        }
    }

    /// Whether the slot holds a half that lowers to a core term.
    ///
    /// # Specification
    /// - requires: the slot's member coordinates are interpreted in this
    ///   lowering run.
    /// - ensures: [`Owed::Nothing`] for the prelude's `Eq.generic`, which
    ///   stands for a derivation and lowers to no core term, and for a witness
    ///   of a member that carries a refusal, whatever its other half — the
    ///   refusal is reported where the member is written; otherwise
    ///   [`Owed::Owed`] when either half is present and is not a top-level
    ///   `oper`'s, which lowers to no core term.
    /// - provides: the halves whose absence [`Self::outcome`] refuses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function whose halves the mint left unminted owes a
    ///   declaration; reading a top-level `oper` as owing one would refuse
    ///   every such declaration across the corpus, and reading a model witness
    ///   of a refused member as owing one reports the refusal twice.
    /// - witness: `gandr-surface-lowering::lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_refused_member_of_a_model_is_refused_once_1081`
    #[spec(
        ensures: |ret| (ret == Owed::Owed) == (
            slot.role != Role::Generic
            && ![slot.signature, slot.definition].into_iter().any(|half| matches!(half,
                Maybe::Present(Half { operand: Operand::Member(target), .. })
                    if self.cx().collected.slots.get(usize::from(target)).is_some_and(|member| matches!(member.refusal, Maybe::Present(_)))))
            && [slot.signature, slot.definition].into_iter().any(|half| matches!(half,
                Maybe::Present(Half { operand: Operand::Written(_) | Operand::Function | Operand::Member(_) | Operand::Data(_) | Operand::Words(_) | Operand::Terms(_) | Operand::Loop { .. } | Operand::Operation | Operand::Derived | Operand::Presented | Operand::Code | Operand::Model(_), .. })))
        ),
    )]
    fn lowers_a_half(
        &self,
        slot: &DeclarationSlot<'source>,
    ) -> Owed
    {
        let halves = [slot.signature, slot.definition];
        let restates_a_refusal = halves.into_iter().any(|half| {
            matches!(half, Maybe::Present(Half { operand: Operand::Member(target), .. })
                if self
                    .cx().collected
                    .slots
                    .get(usize::from(target))
                    .is_some_and(|member| matches!(member.refusal, Maybe::Present(_))))
        });
        let owed = slot.role != Role::Generic
            && !restates_a_refusal
            && halves.into_iter().any(|half| match half {
                Maybe::Present(Half {
                    operand: Operand::Signature | Operand::World,
                    ..
                })
                | Maybe::Absent(_) => false,
                Maybe::Present(Half {
                    operand:
                        Operand::Written(_)
                        | Operand::Function
                        | Operand::Member(_)
                        | Operand::Data(_)
                        | Operand::Words(_)
                        | Operand::Terms(_)
                        | Operand::Loop { .. }
                        | Operand::Operation
                        | Operand::Derived
                        | Operand::Presented
                        | Operand::Code
                        | Operand::Model(_),
                    ..
                }) => true,
            });
        if owed { Owed::Owed } else { Owed::Nothing }
    }

    /// What the slot at `position` amounts to by its own halves, whatever
    /// module it belongs to.
    ///
    /// # Specification
    /// - requires: the slot and its member coordinates are interpreted in this
    ///   lowering run.
    /// - ensures: a stored refusal takes precedence, then a refusal a check
    ///   after minting filed; a definition written `Eq.generic(T)` is the
    ///   equality derived for `T`, and the prelude's `Eq.generic` itself is
    ///   unminted; a world declaration is the world it names; a data
    ///   declaration, or a described family the decoder admitted, `Theory`
    ///   among them, is the index of its minted signature; an operation, a
    ///   derived rule and a `theory` block's definition are each the type and
    ///   body minted for it; an abstract slot is the abstract type it lowered
    ///   to, and a kind witness the check of its type member's code at the
    ///   kind; otherwise the available signature — written, a function tail's,
    ///   the type a model derives, or the annotation an unsigned definition's
    ///   whole value is written under — and body select Completed, Uncompleted
    ///   or Bodied, but a definition written as a value or a function tail
    ///   whose body did not mint is the body's absence, which [`Self::outcome`]
    ///   refuses by name, never an obligation the signature owes (#6113).
    /// - provides: the declaration outcome without manufacturing absent halves.
    /// - fails: a refused member witness is Unminted; if neither half exists,
    ///   the signature’s absence is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three successful half combinations remain
    ///   distinct from a stored refusal, and an ascription witness does not
    ///   resurrect a refused member. Explicit signatures keep precedence over
    ///   derived ones.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `gandr-surface-lowering::lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `gandr-surface-lowering::tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
    /// - witness: `gandr-surface-lowering::tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `gandr-surface-lowering::lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `gandr-surface-lowering::tests::modules::opaque_ascription_seals`
    /// - witness: `gandr-surface-lowering::tests::modules::an_abstract_component_kinds_at_a_universe`
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotated_definition_value_is_signed_by_its_annotation_1107`
    /// - witness: `gandr-surface-lowering::lower::tests::a_written_definition_minting_no_body_is_refused_by_name_6113`
    #[spec(
        ensures: |ret| {
            if let Maybe::Present((_at, refusal)) = slot.refusal {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
            }
            else if let Some(&refusal) = self.cx().faults.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
            }
            else if let Some(&(declared_type, body)) = self.cx().generics.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Completed { declared_type, body })
            }
            else if slot.role == Role::Generic {
                ret == Maybe::Absent(lowered::Absent::Unminted)
            }
            else if let Maybe::Present(Half { operand: Operand::World, .. }) = slot.definition {
                ret == Maybe::Present(DeclarationOutcome::World)
            }
            else if let Maybe::Present(Half { operand: Operand::Data(form), .. }) = slot.definition {
                ret == self.cx().signatures.get(&form).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Maybe::Present(Half { operand: Operand::Words(words), .. }) = slot.definition {
                ret == self.cx().worded.get(&words).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Maybe::Present(Half { operand: Operand::Terms(terms), .. }) = slot.definition {
                ret == self.cx().termed.get(&terms).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Maybe::Present(Half { operand: Operand::Loop { .. }, .. }) = slot.definition {
                ret == self.cx().looped.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Some(&index) = self.cx().described.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Data(index))
            }
            else if let Some(&index) = self.cx().codata_described.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Codata(index))
            }
            else if let Maybe::Present(Half { operand: Operand::Operation, .. }) = slot.definition {
                ret == self.cx().operated.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Maybe::Present(Half { operand: Operand::Derived, .. }) = slot.definition {
                ret == self.cx().derivations.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Maybe::Present(Half { operand: Operand::Presented, .. }) = slot.definition {
                ret == self.cx().presented.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Some(&sealing) = self.cx().sealings.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Abstract(sealing))
            }
            else if let Some(&(declared_type, body)) = self.cx().kind_checks.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Completed { declared_type, body })
            }
            else if matches!(slot.definition, Maybe::Present(Half { operand: Operand::Member(target), .. }) if self.cx().collected.slots.get(usize::from(target)).is_some_and(|member| matches!(member.refusal, Maybe::Present(_))))
            {
                ret == Maybe::Absent(lowered::Absent::Unminted)
            }
            else {
                let declared = match slot.signature {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.cx().value_type_at(written.node),
                        | Operand::Function => self.cx().signature_at(half.declaration.node),
                        | Operand::Model(_) => self.cx().modelled.get(&position).copied().map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                        | Operand::Member(_) | Operand::Data(_) | Operand::Words(_) | Operand::Terms(_) | Operand::Loop { .. } | Operand::Operation | Operand::Derived | Operand::Signature | Operand::Presented | Operand::Code | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => self.annotated_type(slot),
                };
                let body = match slot.definition {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.cx().value_at(written.node),
                        | Operand::Function => self.cx().function_body_at(half.declaration.node),
                        | Operand::Member(_) => self
                            .cx().witnessed
                            .get(&position)
                            .copied()
                            .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                        | Operand::Data(_) | Operand::Words(_) | Operand::Terms(_) | Operand::Loop { .. } | Operand::Operation | Operand::Derived | Operand::Signature | Operand::Presented | Operand::Code | Operand::Model(_) | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
                };
                let written = matches!(
                    slot.definition,
                    Maybe::Present(Half { operand: Operand::Written(_) | Operand::Function, .. })
                );
                match ret {
                    | Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body: value,
                    }) => {
                        declared == Maybe::Present(declared_type) && body == Maybe::Present(value)
                    },
                    | Maybe::Present(DeclarationOutcome::Uncompleted { declared_type }) => {
                        declared == Maybe::Present(declared_type)
                            && matches!(body, Maybe::Absent(_))
                            && !written
                    },
                    | Maybe::Present(DeclarationOutcome::Bodied { body: value }) => {
                        matches!(declared, Maybe::Absent(_)) && body == Maybe::Present(value)
                    },
                    | Maybe::Absent(reason) => {
                        (declared == Maybe::Absent(reason) && matches!(body, Maybe::Absent(_)))
                            || (written
                                && matches!(declared, Maybe::Present(_))
                                && body == Maybe::Absent(reason))
                    },
                    | Maybe::Present(DeclarationOutcome::Refused(_) | DeclarationOutcome::Data(_) | DeclarationOutcome::Codata(_) | DeclarationOutcome::Abstract(_) | DeclarationOutcome::World) => false,
                }
            }
        },
    )]
    fn own_outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        if let Maybe::Present((_at, refusal)) = slot.refusal {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Some(&refusal) = self.cx().faults.get(&position) {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Some(&(declared_type, body)) = self.cx().generics.get(&position) {
            return Maybe::Present(DeclarationOutcome::Completed {
                declared_type,
                body,
            });
        }
        if slot.role == Role::Generic {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        if let Maybe::Present(Half {
            operand: Operand::World,
            ..
        }) = slot.definition
        {
            return Maybe::Present(DeclarationOutcome::World);
        }
        if let Maybe::Present(Half {
            operand: Operand::Data(form),
            ..
        }) = slot.definition
        {
            return self
                .cx()
                .signatures
                .get(&form)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Maybe::Present(Half {
            operand: Operand::Words(words),
            ..
        }) = slot.definition
        {
            return self
                .cx()
                .worded
                .get(&words)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Maybe::Present(Half {
            operand: Operand::Terms(terms),
            ..
        }) = slot.definition
        {
            return self
                .cx()
                .termed
                .get(&terms)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Maybe::Present(Half {
            operand: Operand::Loop { .. },
            ..
        }) = slot.definition
        {
            return self.cx().looped.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Some(&index) = self.cx().described.get(&position) {
            return Maybe::Present(DeclarationOutcome::Data(index));
        }
        if let Some(&index) = self.cx().codata_described.get(&position) {
            return Maybe::Present(DeclarationOutcome::Codata(index));
        }
        if let Maybe::Present(Half {
            operand: Operand::Operation,
            ..
        }) = slot.definition
        {
            return self.cx().operated.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Maybe::Present(Half {
            operand: Operand::Derived,
            ..
        }) = slot.definition
        {
            return self.cx().derivations.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Maybe::Present(Half {
            operand: Operand::Presented,
            ..
        }) = slot.definition
        {
            return self.cx().presented.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Some(&sealing) = self.cx().sealings.get(&position) {
            return Maybe::Present(DeclarationOutcome::Abstract(sealing));
        }
        if let Some(&(declared_type, body)) = self.cx().kind_checks.get(&position) {
            return Maybe::Present(DeclarationOutcome::Completed {
                declared_type,
                body,
            });
        }
        if let Maybe::Present(Half {
            operand: Operand::Member(target),
            ..
        }) = slot.definition
            && let Some(Maybe::Present(_)) = self
                .cx()
                .collected
                .slots
                .get(usize::from(target))
                .map(|member| member.refusal)
        {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let declared = match slot.signature {
            Maybe::Present(half) => match half.operand {
                Operand::Written(written) => self.cx().value_type_at(written.node),
                Operand::Function => self.cx().signature_at(half.declaration.node),
                Operand::Model(_) => self
                    .cx()
                    .modelled
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                Operand::Member(_)
                | Operand::Data(_)
                | Operand::Words(_)
                | Operand::Terms(_)
                | Operand::Loop { .. }
                | Operand::Operation
                | Operand::Derived
                | Operand::Signature
                | Operand::Presented
                | Operand::Code
                | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
            },
            Maybe::Absent(_) => self.annotated_type(slot),
        };
        let body = match slot.definition {
            Maybe::Present(half) => match half.operand {
                Operand::Written(written) => self.cx().value_at(written.node),
                Operand::Function => self.cx().function_body_at(half.declaration.node),
                Operand::Member(_) => self
                    .cx()
                    .witnessed
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                Operand::Data(_)
                | Operand::Words(_)
                | Operand::Terms(_)
                | Operand::Loop { .. }
                | Operand::Operation
                | Operand::Derived
                | Operand::Signature
                | Operand::Presented
                | Operand::Code
                | Operand::Model(_)
                | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
            },
            Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        match (declared, body) {
            (Maybe::Present(declared_type), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            // A definition written as a value or a function tail whose body
            // did not mint leaves the signature nothing to complete: the
            // outcome refuses it by name, never as an obligation (#6113).
            (Maybe::Present(_), Maybe::Absent(reason))
                if matches!(
                    slot.definition,
                    Maybe::Present(Half {
                        operand: Operand::Written(_) | Operand::Function,
                        ..
                    })
                ) =>
            {
                Maybe::Absent(reason)
            },
            (Maybe::Present(declared_type), Maybe::Absent(_)) => {
                Maybe::Present(DeclarationOutcome::Uncompleted { declared_type })
            },
            (Maybe::Absent(_), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Bodied { body })
            },
            (Maybe::Absent(reason), Maybe::Absent(_)) => Maybe::Absent(reason),
        }
    }

    /// The type an unsigned definition's whole value is annotated with, `T`
    /// of `def x = (e : T)`.
    ///
    /// # Specification
    /// - requires: the mint sweep has minted the annotation's type, if it
    ///   could.
    /// - ensures: `T` as minted, where `slot`'s definition is written and
    ///   `Native::sign_definitions` recorded its annotation; the unminted
    ///   absence otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::own_outcome`].
    /// - witness: `gandr-surface-lowering::lower::native::tests::an_annotated_definition_value_is_signed_by_its_annotation_1107`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(slot.definition, Maybe::Present(Half { operand: Operand::Written(written), .. }) if self.cx().annotated_definitions.contains_key(&written.node)))]
    fn annotated_type(
        &self,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let Maybe::Present(Half {
            operand: Operand::Written(written),
            ..
        }) = slot.definition
        else {
            return unminted;
        };
        self.cx()
            .annotated_definitions
            .get(&written.node)
            .map_or(unminted, |&classifier| self.cx().value_type_at(classifier))
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Carry each refused manifest type component's refusal to every
    /// declaration whose type names it.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: a declaration owning a type head that stands for a manifest
    ///   component whose type refused holds that refusal too, at the head's
    ///   position, so it keeps the lowest-positioned refusal it has; the
    ///   components are taken in signature order, so a component naming an
    ///   earlier refused one passes the refusal on.
    /// - provides: the rule that a declaration is not minted over a type that
    ///   did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of manifest aliases carries the original
    ///   located refusal into a member even when its body has independently
    ///   failed; the unrelated following declaration still lowers.
    /// - witness: `gandr-surface-lowering::tests::modules::manifest_refusals_propagate_transitively_before_minting`
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body sorts the manifest references and visits each once; the check reads each once and its neighbour once"
        )
    )]
    #[spec(
        captures: before = (self.cx().manifests.len(), self.cx().collected.slots.len()),
        ensures: |_| {
            self.cx().manifests.len() == before.0 && self.cx().collected.slots.len() == before.1 && self.cx().manifests.windows(2).all(|pair| match *pair { [left, right] => left.0 <= right.0, _ => false }) && self.cx().manifests.iter().all(|&(held, head)| { if !matches!(self.cx().collected.slots.get(usize::from(held)), Some(slot) if matches!(slot.refusal, Maybe::Present(_))) { return true; } match self.cx().collected.owner_of(head) { Maybe::Absent(_) => true, Maybe::Present(owner) => self.cx().collected.slots.get(usize::from(owner)).is_none_or(|slot| matches!(slot.refusal, Maybe::Present((at, _)) if at <= head)) } })
        },
    )]
    #[inline]
    pub fn propagate_manifests(&mut self)
    {
        let mut named = core::mem::take(&mut self.cx_mut().manifests);
        named.sort_by_key(|&(held, _head)| held);
        for &(held, head) in &named {
            let Some(Maybe::Present((_at, refusal))) = self
                .cx()
                .collected
                .slots
                .get(usize::from(held))
                .map(|slot| slot.refusal)
            else {
                continue;
            };
            let Maybe::Present(owner) = self.cx().collected.owner_of(head)
            else {
                continue;
            };
            if let Some(slot) = self.cx_mut().collected.slots.get_mut(usize::from(owner)) {
                slot.refuse(head, refusal);
            }
        }
        self.cx_mut().manifests = named;
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
    /// One stratum item per module, in pre-order.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each module's path, its form's bytes, the value components
    ///   and nested modules it exports in export order — a value component with
    ///   the constant a reference reads, the witness an opaque ascription
    ///   exports in its member's place — each exported type component that
    ///   reads a type with the value type it lowered to, or the reason it has
    ///   none ([`Self::manifest_value`]), each sealed one with its atom, and
    ///   whether matching coerced its body; a hidden member appears in no item.
    /// - provides: the stratum half of [`LoweredModule`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested paths retain their member names, an ascription
    ///   exports only its selected values and modules, manifest components keep
    ///   their lowered type or their explicit Unlowered or Computation status,
    ///   and a sealed module exports its atoms and its witnesses.
    /// - witness: `gandr-surface-lowering::tests::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `gandr-surface-lowering::tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::opaque_ascription_seals`
    /// - witness: `gandr-surface-lowering::tests::modules::a_signed_member_of_a_sealed_module_exports_its_witness`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
    #[spec(
        ensures: |ret| {
            ret.len() == self.cx().collected.structures.len()
                && ret
                    .iter()
                    .enumerate()
                    .zip(&self.cx().collected.structures)
                    .all(|((position, lowered), structure)| {
                        if lowered.path().last() != Some(&structure.name)
                            || lowered.span() != structure.declared_by.span
                            || lowered.coerced() != structure.coerced
                        {
                            return false;
                        }
                        let mut values = lowered.values().iter();
                        let mut modules = lowered.modules().iter();
                        for &export in &structure.exports {
                            match export {
                                | Member::Slot(slot) => {
                                    let read = self.cx().collected.exported_read(StructureIndex::from(position), slot);
                                    if self.cx().collected.slots.get(usize::from(slot)).is_some_and(
                                        |member| {
                                            !values.next().is_some_and(|value| {
                                                value.name == member.name
                                                    && usize::from(value.constant) == usize::from(read)
                                            })
                                        },
                                    ) {
                                        return false;
                                    }
                                },
                                | Member::Module(nested) => {
                                    if self
                                        .cx().collected
                                        .structures
                                        .get(usize::from(nested))
                                        .is_some_and(|member| modules.next() != Some(&member.name))
                                    {
                                        return false;
                                    }
                                },
                            }
                        }
                        let mut types = lowered.types().iter();
                        let mut sealed = lowered.sealed().iter();
                        let stated = structure.exported_types().iter().all(|component| match component.meaning {
                            | TypeMeaning::Manifest(_) | TypeMeaning::Instantiated { .. } => types.next().is_some_and(|lowered| {
                                lowered.name == component.name && lowered.defined == self.manifest_value(component.meaning)
                            }),
                            | TypeMeaning::Sealed => sealed.next().is_some_and(|lowered| {
                                lowered.name == component.name
                                    && usize::from(lowered.atom) == usize::from(component.held)
                            }),
                            | TypeMeaning::Family(_) => true,
                        });
                        stated
                            && lowered.stratum() == structure.stratum
                            && values.next().is_none()
                            && modules.next().is_none()
                            && types.next().is_none()
                            && sealed.next().is_none()
                    })
        },
    )]
    #[inline]
    #[must_use]
    pub fn structures(&self) -> Vec<LoweredStructure<'source>>
    {
        let mut lowered = Vec::with_capacity(self.cx().collected.structures.len());
        for (position, structure) in self.cx().collected.structures.iter().enumerate() {
            let mut values = Vec::new();
            let mut modules = Vec::new();
            for &export in &structure.exports {
                match export {
                    Member::Slot(slot) => {
                        let read = self
                            .cx()
                            .collected
                            .exported_read(StructureIndex::from(position), slot);
                        if let Some(member) = self.cx().collected.slots.get(usize::from(slot))
                            && let Some(reader) = self.cx().collected.slots.get(usize::from(read))
                        {
                            values.push(ValueComponent {
                                name: member.name,
                                constant: reader.constant,
                            });
                        }
                    },
                    Member::Module(nested) => {
                        if let Some(member) =
                            self.cx().collected.structures.get(usize::from(nested))
                        {
                            modules.push(member.name);
                        }
                    },
                }
            }
            let mut types = Vec::new();
            let mut sealed = Vec::new();
            for component in structure.exported_types() {
                match component.meaning {
                    TypeMeaning::Manifest(_) | TypeMeaning::Instantiated { .. } => {
                        types.push(ManifestComponent {
                            name: component.name,
                            defined: self.manifest_value(component.meaning),
                        });
                    },
                    TypeMeaning::Sealed => {
                        if let Some(atom) =
                            self.cx().collected.slots.get(usize::from(component.held))
                        {
                            sealed.push(SealedComponent {
                                name: component.name,
                                atom: atom.constant,
                            });
                        }
                    },
                    TypeMeaning::Family(_) => {},
                }
            }
            lowered.push(LoweredStructure::new(
                self.cx()
                    .collected
                    .path(Container::Module(StructureIndex::from(position))),
                structure.declared_by.span,
                values,
                modules,
                types,
                sealed,
                structure.coerced,
                structure.stratum,
            ));
        }

        lowered
    }

    /// The value type a manifest or an instance's type component reads, or
    /// why it has none.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: the value type the component's definition lowered to, its
    ///   template's renamed by the application for an instance's; the
    ///   computation reason for a definition that lowered to a computation
    ///   type; the unlowered reason otherwise, a sealed or family component
    ///   too.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value member exports its type, a computation member
    ///   its reason, and a refused member the unlowered reason.
    /// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(_) => matches!(meaning, TypeMeaning::Manifest(_) | TypeMeaning::Instantiated { .. }),
        Maybe::Absent(manifest_type::Absent::Computation) => matches!(
            meaning,
            TypeMeaning::Manifest(defined) | TypeMeaning::Instantiated { defined, .. }
                if self.cx().computation_members.contains(&defined.node)
        ),
        Maybe::Absent(manifest_type::Absent::Unlowered) => true,
    })]
    fn manifest_value(
        &self,
        meaning: TypeMeaning,
    ) -> Maybe<ValueTypeId, manifest_type::Absent>
    {
        let unlowered = Maybe::Absent(manifest_type::Absent::Unlowered);
        let computation = Maybe::Absent(manifest_type::Absent::Computation);
        match meaning {
            TypeMeaning::Manifest(defined) => match self.cx().value_type_at(defined.node) {
                Maybe::Present(id) => Maybe::Present(id),
                Maybe::Absent(_) => match self.cx().comp_type_at(defined.node) {
                    Maybe::Present(_) if self.cx().computation_members.contains(&defined.node) => {
                        computation
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => unlowered,
                },
            },
            TypeMeaning::Instantiated { defined, instance } => {
                match self.cx().instance_types.get(&(instance, defined.node)) {
                    Some(&InstanceType::Value(id)) => Maybe::Present(id),
                    Some(&InstanceType::Computation(_)) => computation,
                    None => unlowered,
                }
            },
            TypeMeaning::Sealed | TypeMeaning::Family(_) => unlowered,
        }
    }

    /// The binders in scope at each node the lowering read under a binder:
    /// the scope's frames, beside each such node's span and its reading's
    /// frame; after the closure's table when `resumed` gives it, from the
    /// block it marks on.
    ///
    /// # Specification
    /// - requires: every source is lowered; `resumed`, when given, marks where
    ///   the lowering resumed after a closure's.
    /// - ensures: `Lowerer::in_scope` over this lowering's scope and one span
    ///   per node whose reading names an inner frame, a node of a refused
    ///   declaration included; after a closure, `Lowerer::in_scope_after` over
    ///   the closure's table and the nodes of the blocks past its mark.
    /// - provides: the table [`LoweredModule::in_scope`] keeps.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table's own builder and query carry the
    ///   predicates.
    /// - intension: one pass over the node readings past the mark.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::InScope::binders_at`].
    /// - witness: `gandr-surface-lowering::tests::scopes::the_binders_in_scope_are_kept_for_a_refused_declaration_831`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[inline]
    #[must_use]
    pub fn in_scope(
        &self,
        resumed: Option<Resumed<'_, '_>>,
    ) -> crate::InScope
    {
        let from = resumed.map_or_else(|| LayoutBlock::from(0_usize), |resumed| resumed.blocks);
        let read = self
            .cx()
            .tree
            .positions_from(from)
            .filter_map(|position| match self.cx().readings.get(position)?.frame() {
                Frame::Inner(frame) => self
                    .cx()
                    .tree
                    .node(position)
                    .map(|node| (node.span(), frame)),
                Frame::Outermost => None,
            })
            .collect();
        match resumed {
            Some(resumed) => self
                .cx()
                .scope
                .in_scope_after(&resumed.finished.in_scope, read),
            None => self.cx().scope.in_scope(read),
        }
    }

    /// Where a lowering continued from this one, a closure's suspended
    /// lowering that finished alone as `finished`, onto `origins` begins.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn resumed<'finished>(
        &self,
        finished: &'finished Finished<'source>,
        origins: &OriginTable,
    ) -> Resumed<'finished, 'source>
    {
        Resumed {
            finished,
            slots: self.cx().collected.slots.len(),
            blocks: self.cx().readings.blocks(),
            values: origins.values().len(),
            resolved: self.cx().resolutions.len(),
            declared: self.cx().collected.declared_uses.len(),
        }
    }
}

/// What reading one attribute produced, short of a refusal.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A filed entry has passed registry and payload checks; an
///   unlowered payload contributes no entry or seen-name update.
/// - provides: The non-refusal outcome of reading one attribute.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The written attribute and seen-name list are absent;
///   `read_attribute` states the executable filing and state-update relation.
///
/// # Adequacy
/// - hypothesis: L3 — valid entries are filed under the declaration key, while
///   a refused declaration can still retain an independently valid payload.
/// - witness: `gandr-surface-lowering::lower::tests::an_attribute_is_filed_under_its_declaration_key`
/// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Filing
{
    /// The entry to file, the declarations a `respects` or `entry` payload
    /// names and the members an `identity` payload names: each empty for
    /// every other attribute, and never empty for its own, whose payload
    /// names at least one, an `identity`'s two or three.
    Filed
    {
        /// The entry.
        entry: AttributeEntry,
        /// The declarations its payload names, in written order.
        named: Vec<ConstantIndex>,
        /// The interface members its payload names, as the components the
        /// payload lowered them to, in written order.
        members: Vec<ValueId>,
        /// The spelling of a payload its schema reads unquoted, present
        /// exactly for [`AttributeSchema::Spelled`].
        spelled: Option<String>,
    },
    /// Nothing: the payload did not lower, which only a payload that itself
    /// refused leaves behind.
    Unlowered,
}

/// The parameter of a lambda: exactly one identifier between parentheses,
/// with the type written after its `:`, if one is.
///
/// # Specification
/// - requires: `cursor` stands just past the lambda's `fun`.
/// - ensures: the one parameter's tile and the one operand its `:` writes, with
///   the cursor past the closing parenthesis.
/// - provides: the binder reading of the lambda.
/// - fails: yields the arity refusal for any parameter count but one, the
///   extra-operand refusal for a `:` over more than one type, and a
///   misplaced-tile refusal for a parameter list out of shape or a second `:`.
/// - panics: none.
///
/// # Errors
/// The lambda's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and multiple binders select the documented
///   arity boundary; a successful header, typed or not, consumes its closing
///   parenthesis but not the following body.
/// - witness: `gandr-surface-lowering::lower::tests::parameter_headers_preserve_the_body_and_locate_refusals`
/// - witness: `gandr-surface-lowering::lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
#[spec(
    captures: input = cursor.clone(),
    ensures: |ret| {
        ret.as_ref().map_or(true, |&(binder, declared)| {
            let mut input = input.clone();
            if matches!(input.tile(TileName::PAREN_OPEN), Maybe::Absent(_)) {
                return false;
            }
            let mut seen = false;
            let mut typed = None;
            loop {
                match input.read() {
                    | Maybe::Present(Piece::Tile {
                        label: TileName::IDENTIFIER,
                        at,
                    }) => {
                        if seen || at != binder {
                            return false;
                        }
                        seen = true;
                    },
                    | Maybe::Present(Piece::Tile {
                        label: TileName::COMMA | TileName::COLON,
                        ..
                    }) => {},
                    | Maybe::Present(Piece::Operand(operand)) => {
                        if typed.is_some() {
                            return false;
                        }
                        typed = Some(operand);
                    },
                    | Maybe::Present(Piece::Tile {
                        label: TileName::PAREN_CLOSE,
                        ..
                    }) => {
                        return seen
                            && typed == declared
                            && cursor.peek() == input.peek()
                            && cursor.here() == input.here();
                    },
                    | _ => return false,
                }
            }
        })
    },
)]
#[inline]
pub fn parameter<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
) -> Result<(Placed, Option<Placed>), LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    let mut first: Option<Placed> = None;
    let mut declared: Option<Placed> = None;
    let mut count = 0_usize;
    loop {
        if let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER) {
            count = count.saturating_add(1_usize);
            first = first.or(Some(binder));
            continue;
        }
        if let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
            continue;
        }
        if declared.is_none()
            && let Maybe::Present(_) = cursor.tile(TileName::COLON)
        {
            declared = Some(site.one(cursor.operands())?);
            continue;
        }
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
            break;
        }
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    match first {
        Some(binder) if count == 1_usize => Ok((binder, declared)),
        Some(_) | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
    }
}

/// The keywords a block statement opens with: `let`, `var`, `import` and
/// `module`.
const STATEMENT_KEYWORDS: [TileName; 4_usize] = [
    TileName::LET,
    TileName::VAR,
    TileName::IMPORT,
    TileName::MODULE,
];

/// The argument lists a qualified type writes after its member, `(Integer)` in
/// `M.F(Integer)`, read into `written`, when it writes them (#3051): the first,
/// and the second that applies the first call's result once more,
/// `(x)` in `Standard.subTy(a, s)(x)` (#5213).
///
/// # Specification
/// - requires: `pieces` is the reading of a type path covering `span`.
/// - ensures: the stretches of `written` the first list's and the second list's
///   arguments fill, each in written order, for a path whose pieces hold a `(`;
///   none for a list the path does not write, `written` unchanged by a path
///   that writes none.
/// - fails: as [`arguments`].
/// - panics: none.
/// - executable: none — each list's reading is [`arguments`]'s, whose own
///   predicate states it.
///
/// # Errors
/// The list's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — `M.F(Integer)` reads one argument, `M.T` none, and
///   `M.f(a)(b)` one in each list.
/// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
/// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
fn path_arguments<'source>(
    site: Site,
    pieces: &[Piece],
    span: ByteSpan,
    written: &mut ByForm<NodeIndex>,
) -> Result<(Option<Stretch>, Option<Stretch>), LoweringRefusal<'source>>
{
    let mut cursor = Cursor::new(pieces, span);
    loop {
        if let Maybe::Present(Piece::Tile {
            label: TileName::PAREN_OPEN,
            ..
        }) = cursor.peek()
        {
            let start = written.entries().len();
            let again = argument_lists(site, &mut cursor, written)?;
            let first = Stretch {
                start,
                end: again.map_or_else(|| written.entries().len(), |again| again.start),
            };
            return Ok((Some(first), again));
        }
        if let Maybe::Absent(_) = cursor.read() {
            return Ok((None, None));
        }
    }
}

/// Refuse the argument list `applied` a qualified type writes after a member
/// that takes none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success for no list.
/// - fails: the arity boundary at `site`, naming the count written, for a list.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::OutOfFragment`] with the arity boundary.
///
/// # Adequacy
/// - hypothesis: L3 — `M.T(Integer)` over an unparameterised member is refused
///   by its count.
/// - witness: `gandr-surface-lowering::tests::modules::a_module_s_family_is_applied_through_its_name_3051`
#[spec(ensures: |ret| ret.is_ok() == applied.is_none())]
fn unapplied<'source>(
    site: Site,
    applied: Option<Stretch>,
) -> Result<(), LoweringRefusal<'source>>
{
    applied.map_or(Ok(()), |written| {
        Err(site.out(FragmentBoundary::Arity(OperandCount::from(
            written.end.saturating_sub(written.start),
        ))))
    })
}

/// Read the argument lists a call in a type writes into `written`: the first,
/// and the second that applies the call's result once more, `(b)` in
/// `f(a)(b)`, when the cursor stands at one (#5213).
///
/// # Specification
/// - requires: `cursor` stands at the first list's `(`.
/// - ensures: the first list's arguments appended to `written`, then the
///   stretch of the second list's when it writes one, with the cursor past the
///   last `)` and nothing after it.
/// - fails: as [`delimited`].
/// - panics: none.
/// - executable: none — each list's reading is [`delimited_list`]'s.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — `f(a)` reads one list, and `f(a)(b)` reads two.
/// - witness: `gandr-surface-lowering::tests::modules::a_module_s_function_is_called_in_a_type_5213`
fn argument_lists<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut ByForm<NodeIndex>,
) -> Result<Option<Stretch>, LoweringRefusal<'source>>
{
    delimited_list(
        site,
        cursor,
        written,
        TileName::PAREN_OPEN,
        TileName::PAREN_CLOSE,
    )?;
    let opens = matches!(
        cursor.peek(),
        Maybe::Present(Piece::Tile {
            label: TileName::PAREN_OPEN,
            ..
        })
    );
    if !opens {
        exhausted(site, cursor)?;
        return Ok(None);
    }
    let start = written.entries().len();
    arguments(site, cursor, written)?;
    Ok(Some(Stretch {
        start,
        end: written.entries().len(),
    }))
}

/// The two operands of the product `site`, `A * B`, the sum `site`, `A + B`,
/// or the lazy product `site`, `C & D`, in written order; `former` names which.
///
/// # Specification
/// - requires: `cursor` holds the pieces of a form of `former` at `site`.
/// - ensures: one operand, the `*` tile of a product, the `+` tile of a sum or
///   the `&` tile of a lazy product, and one operand, nothing after them.
/// - provides: the shape check every link of a product, a sum or a lazy product
///   chain shares.
/// - fails: either hole's own refusal, and a misplaced-tile or extra-operand
///   refusal for a link out of shape.
/// - panics: none.
///
/// # Errors
/// The link's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a well-shaped product and a well-shaped sum answer their
///   operands in order.
/// - witness: `gandr-surface-lowering::lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `gandr-surface-lowering::lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&[first, second]| first != second))]
fn halves<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    former: Former,
) -> Result<[NodeIndex; 2], LoweringRefusal<'source>>
{
    let tile = if former == Former::SumType {
        TileName::PLUS
    }
    else if former == Former::LazyProductType {
        TileName::AMPERSAND
    }
    else {
        TileName::STAR
    };
    let first = site.one(cursor.operands())?;
    closed(site, cursor, tile)?;
    let second = site.one(cursor.operands())?;
    exhausted(site, cursor)?;

    Ok([first.node, second.node])
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: nothing; the function is total over the former vocabulary.
/// - ensures: exactly the value-producing formers answer affirmatively — a
///   name, a capitalised name, a number, a string, the unit, a parenthesised
///   expression, a thunk, a telescope value, a list literal and an injection —
///   the reserved tuple among them, since a reserved form is a value the
///   fragment declines rather than a form of another sort, and keeping the two
///   apart is what lets an attribute payload written as a computation be
///   reported as a non-value rather than as a sort error.
/// - provides: the guard the attribute payload reading takes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the vocabulary is a finite class, enumerated exhaustively
///   with each former's exact answer asserted, so promoting or demoting any
///   single former breaks one row.
/// - witness: `gandr-surface-lowering::lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[spec(
    ensures: |ret| {
        ret.0
            == matches!(
                former,
                Former::Name
                    | Former::Constructor
                    | Former::Number
                    | Former::Boolean
                    | Former::Text
                    | Former::Character
                    | Former::Parenthesized
                    | Former::Thunk
                    | Former::Telescope
                    | Former::List
                    | Former::PackModel
                    | Former::Injection
            )
    },
)]
#[inline]
#[must_use]
pub const fn is_value_form(former: Former) -> ValueForm
{
    ValueForm(matches!(
        former,
        Former::Name
            | Former::Constructor
            | Former::Number
            | Former::Boolean
            | Former::Text
            | Former::Character
            | Former::Parenthesized
            | Former::Thunk
            | Former::Telescope
            | Former::List
            | Former::PackModel
            | Former::Injection
    ))
}

/// Read a number written with an integer width: decimal digits, then `u32`,
/// `u64`, `i32` or `i64`.
///
/// # Specification
/// - requires: nothing; any text is admissible.
/// - ensures: digits that fit the width the suffix names read as that width's
///   literal, leading zeros dropped.
/// - fails: [`literal::Absent::OutsideWidth`] for an integer width's suffix
///   after digits that do not fit it, or after a fraction or an exponent;
///   [`literal::Absent::Malformed`] for a text with no integer width's suffix,
///   an `f64` or `f32` one included.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each width's literal reads at its extremes and with
///   leading zeros; one past each extreme, a fraction and an exponent fall
///   outside the width; the floating suffixes, an unknown suffix and a bare
///   number are no integer width's lexeme.
/// - witness: `gandr-surface-lowering::lower::tests::a_typed_number_is_its_value_at_its_width`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        match spelled.split_at_checked(spelled.len().saturating_sub(3)) {
            | Some((digits, suffix)) => match ret {
                | Maybe::Present(Literal::Fixed(fixed)) => {
                    let unpadded = digits.trim_start_matches('0');
                    matches!((fixed.width(), suffix), (IntegerWidth::U32, "u32") | (IntegerWidth::U64, "u64") | (IntegerWidth::I32, "i32") | (IntegerWidth::I64, "i64"))
                        && fixed.to_decimal() == if unpadded.is_empty() { "0" } else { unpadded }
                },
                | Maybe::Absent(literal::Absent::OutsideWidth) => matches!(suffix, "u32" | "u64" | "i32" | "i64"),
                | Maybe::Absent(literal::Absent::Malformed) => !matches!(suffix, "u32" | "u64" | "i32" | "i64"),
                | _ => false,
            },
            | None => matches!(ret, Maybe::Absent(literal::Absent::Malformed)),
        }
    },
)]
#[inline]
pub fn typed_number_literal(text: SourceFragment<'_>) -> Maybe<Literal, literal::Absent>
{
    let spelled: &str = text.as_ref();
    let Some((digits, suffix)) = spelled.split_at_checked(spelled.len().saturating_sub(3))
    else {
        return Maybe::Absent(literal::Absent::Malformed);
    };
    if !matches!(suffix, "u32" | "u64" | "i32" | "i64") {
        return Maybe::Absent(literal::Absent::Malformed);
    }
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Maybe::Absent(literal::Absent::OutsideWidth);
    }
    let fixed = match suffix {
        "u32" => digits.parse::<u32>().map(FixedInteger::U32),
        "u64" => digits.parse::<u64>().map(FixedInteger::U64),
        "i32" => digits.parse::<i32>().map(FixedInteger::I32),
        "i64" => digits.parse::<i64>().map(FixedInteger::I64),
        _ => return Maybe::Absent(literal::Absent::Malformed),
    };
    fixed.map_or(Maybe::Absent(literal::Absent::OutsideWidth), |fixed| {
        Maybe::Present(Literal::Fixed(fixed))
    })
}

/// Whether `text` is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: the input is interpreted as an unsigned numeric lexeme.
/// - ensures: a decimal or exponent marker is required; the whole part and each
///   present fraction or exponent contain nonempty ASCII digits, with at most
///   one exponent sign.
/// - provides: the distinction between a fractional number that states no type
///   and a malformed integer spelling.
/// - fails: malformed, unmarked, signed-whole and non-ASCII spellings return
///   false.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent boundaries distinguish unsupported
///   fractional numbers from malformed spellings, including empty fields,
///   repeated markers, exponent signs and non-ASCII digits.
/// - witness: `gandr-surface-lowering::lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `gandr-surface-lowering::lower::tests::a_number_takes_float64_from_its_suffix_or_annotation_1830`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        let mut bytes = spelled.bytes().peekable();
        let digits = |bytes: &mut core::iter::Peekable<core::str::Bytes<'_>>| {
            let present = bytes.peek().is_some_and(u8::is_ascii_digit);
            while bytes.peek().is_some_and(u8::is_ascii_digit) {
                let _digit = bytes.next();
            }
            present
        };
        let whole = digits(&mut bytes);
        let fraction = bytes.next_if_eq(&b'.').is_some();
        let fraction_ok = !fraction || digits(&mut bytes);
        let exponent = bytes.next_if(|&byte| matches!(byte, b'e' | b'E')).is_some();
        let exponent_ok = !exponent || {
            let _sign = bytes.next_if(|&byte| matches!(byte, b'+' | b'-'));
            digits(&mut bytes)
        };
        ret.0
            == (whole
                && (fraction || exponent)
                && fraction_ok
                && exponent_ok
                && bytes.next().is_none())
    },
)]
#[inline]
#[must_use]
pub fn fractional(text: SourceFragment<'_>) -> Fractional
{
    let spelled: &str = text.as_ref();
    let (mantissa, exponent) = spelled
        .split_once(['e', 'E'])
        .map_or((spelled, None), |(left, right)| (left, Some(right)));
    let (whole, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, None), |(left, right)| (left, Some(right)));
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let fraction_ok = fraction.is_none_or(digits);
    let exponent_ok =
        exponent.is_none_or(|part| digits(part.strip_prefix(['+', '-']).unwrap_or(part)));
    let marked = fraction.is_some() || exponent.is_some();

    Fractional(marked && digits(whole) && fraction_ok && exponent_ok)
}

/// The most digits a decimal literal's exact value may spell: an exponent past
/// it would ask the lowering for more digits than any reader reads.
const DECIMAL_DIGITS: usize = 1_usize << 16_u32;

/// The exact decimal value of the unsigned numeric lexeme `text`, a fraction,
/// an exponent or both (#4807).
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a [`fractional`] lexeme `w.f` or `w.fEx` or `wEx`, the
///   canonical non-negative numeric literal of `wf × 10^(x − |f|)`, its digits
///   moved across the point by the exponent; nothing for any other.
/// - fails: [`literal::Absent::Malformed`] for a lexeme [`fractional`] refuses,
///   and for one whose exact value spells more than [`DECIMAL_DIGITS`] digits.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a plain fraction, an exponent above and below the point,
///   an exponent past every digit, trailing and leading zeros, and an exponent
///   past the bound separate each reading from the refusal.
/// - witness: `gandr-surface-lowering::lower::tests::a_decimal_reads_as_its_exact_value_4807`
#[spec(
    ensures: |ret| match ret {
        | Maybe::Present(ref decimal) => fractional(text).0 && decimal.sign() == Sign::NonNegative,
        | Maybe::Absent(absent) => absent == literal::Absent::Malformed,
    },
)]
fn decimal_literal(text: SourceFragment<'_>) -> Maybe<NumericLiteral, literal::Absent>
{
    if !fractional(text).0 {
        return Maybe::Absent(literal::Absent::Malformed);
    }
    let spelled: &str = text.as_ref();
    let (mantissa, exponent) = spelled
        .split_once(['e', 'E'])
        .map_or((spelled, None), |(left, right)| (left, Some(right)));
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let shift = match exponent {
        None => 0_i64,
        Some(written) => match written.parse::<i64>() {
            Ok(shift) => shift,
            Err(_) => return Maybe::Absent(literal::Absent::Malformed),
        },
    };
    // The point stands `point` digits into the whole digit string.
    let digits = alloc::format!("{whole}{fraction}");
    let Some(point) = i64::try_from(whole.len())
        .ok()
        .and_then(|written| written.checked_add(shift))
    else {
        return Maybe::Absent(literal::Absent::Malformed);
    };
    let spelled_digits = i64::try_from(digits.len()).unwrap_or(i64::MAX);
    // The digits the exact value spells: zeros after the point before the
    // written digits, or zeros after them before the point.
    let produced = if point <= 0 {
        point
            .unsigned_abs()
            .saturating_add(spelled_digits.unsigned_abs())
    }
    else {
        point.max(spelled_digits).unsigned_abs()
    };
    if usize::try_from(produced).map_or(true, |produced| produced > DECIMAL_DIGITS) {
        return Maybe::Absent(literal::Absent::Malformed);
    }
    let (integral, fractional_digits) = if point <= 0 {
        let zeros = usize::try_from(point.abs()).unwrap_or_default();
        (
            String::from("0"),
            alloc::format!("{}{digits}", "0".repeat(zeros)),
        )
    }
    else if point >= spelled_digits {
        let zeros = usize::try_from(point.saturating_sub(spelled_digits)).unwrap_or_default();
        (
            alloc::format!("{digits}{}", "0".repeat(zeros)),
            String::new(),
        )
    }
    else {
        let at = usize::try_from(point).unwrap_or_default();
        let (left, right) = digits.split_at(at);
        (String::from(left), String::from(right))
    };
    let (Some(integral), Some(fraction)) = (
        Magnitude::from_decimal_text(integral),
        FractionDigits::from_decimal_text(fractional_digits),
    )
    else {
        return Maybe::Absent(literal::Absent::Malformed);
    };
    Maybe::Present(NumericLiteral::new(Sign::NonNegative, integral, fraction))
}
