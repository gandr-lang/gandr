//! The type of every node of a source a reader can point at: each term its
//! declarations judge, each binder a use resolves to, each type written, and
//! each declaration, spelled and keyed by where the source wrote it.
//!
//! # One typed run per revision a face asks about
//!
//! `TypeTable::of` parses and lowers the source, judges every declaration in
//! the checker's typed run (`gandr_core_checker::type_module`), and keeps the
//! type the run gave each node, spelled through the printer every face shares
//! when a reader asks for it:
//!
//! - **A term** is spelled at the type its innermost judgement gave it — the
//!   type it synthesised, or the type it was checked against when it was only
//!   checked — and, when an outer judgement checked it against a type spelled
//!   otherwise, at that type too, so a mismatched term shows both sides. The
//!   typed run marks a refusal where it stands and goes on, so the terms past a
//!   refusal are typed as well.
//! - **A binder** is spelled at the type of the uses that resolve to it, read
//!   through the origin table's use-to-binder record. A binder no use resolves
//!   to, and any other label — a record or sum type's field, a lazy record's
//!   observation, a record's field, a session action's endpoint — is spelled at
//!   what it labels, read through the origin table's labels: a type's entry at
//!   that type under the binders it is read under, a record's field at its
//!   value's type, an endpoint at the session type the typed run found it
//!   standing at in that action, so each use shows the protocol left to run.
//! - **A pattern** is spelled with what it wrote at the type its place in the
//!   match's scrutinee gives it: a root pattern at the scrutinee's type, a
//!   constructor's field at the field's type read at the family's arguments, a
//!   word pattern's letter, cons and rest at the words' type, a product's or a
//!   sum's components at their own. A constructor's name in a pattern is
//!   spelled at the constructor's type. The lowering keeps where each pattern
//!   and constructor name was written beside the match
//!   ([`CaseOrigin`](gandr_surface_lowering::CaseOrigin)); the typed run judges
//!   the scrutinee before the arms, so a match whose body it refused still
//!   types every pattern of it. The alternative was typing patterns in the
//!   lowering, which knows the scrutinee's type only where the source annotated
//!   it; the choice reverses when the typed run records the type it checked
//!   each arm's bindings at.
//! - **A written type** is spelled at its universe: the level the typed run
//!   formed it at, under the binders it was formed under, and the level it
//!   reads closed where no formation reached it. A type the lowering inserted
//!   takes no entry. A head that stands for a type minted elsewhere — a
//!   manifest component's, a functor instance's, or a functor parameter's
//!   renamed to an argument's — is spelled at the universe of the type it
//!   stands for, read through the origin table's stand-ins. A description a
//!   `ua` names is no core node; it is spelled at the universe its statement's
//!   path lies in.
//! - **A declaration** is spelled at its declared type, at the type its body
//!   synthesised when it states none, and at its universe when it declares
//!   data; a declaration the lowering refused keeps its refusal instead, since
//!   no judgement reached it. Either is keyed by the cross-tree key of each of
//!   its signature and definition forms, so a face holding either form finds
//!   the one declaration both halves make. A `data` family's operation is
//!   declared from the family's own form, so the family's key stays the
//!   family's. A declaration refused for binding again a name an unqualified
//!   import binds answers at none of its sites: every name it writes reads as
//!   the import's, so a type naming its own family would print as the type it
//!   hides.
//! - **A described member** — a `theory` block's sorts, operations, laws and
//!   circuits, a `data` family's constructors, operations and rules, each port
//!   and each node of a rule's sides — is spelled at the type its member states
//!   ([`LoweredModule::described_types`]): the typed run judges none of them,
//!   since the description route reads them. A theory's member is read under
//!   the members before it, named as the theory writes them.
//!
//! The table answers a byte offset with the innermost entry whose span holds
//! it. Among entries of one span a binder comes first, then a written node
//! before an inserted one, then the node judged last, which is the outer one
//! when two nodes share the span.
//!
//! A reader asks about one position, so the table keeps the type nodes and
//! the arena they live in, and spells only the entry it answers with. The
//! alternative was spelling every entry as the table is built: a type laid out
//! for every node the source writes, of which a hover reads one, made spelling
//! half the table's cost.
//!
//! The alternatives were keeping the types in the composition every revision
//! builds, which pays a second judgement of every declaration on every
//! keystroke for a table read only when a reader points, and reading types off
//! the session's resume, which keeps one type per declaration and none for
//! the nodes inside it. The choice reverses when a face reads the table on
//! every revision — inlay hints of every binder's type — and the composition
//! should then carry it from the run that already judges.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::path::Path;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::CodeDefinitions;
use gandr_core_checker::Formations;
use gandr_core_checker::Formed;
use gandr_core_checker::HostGrant;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::TypedModule;
use gandr_core_checker::Typings;
use gandr_core_checker::level_of;
use gandr_core_checker::type_module;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::FieldLabel;
use gandr_core_term::Sort;
use gandr_core_term::TypeImporter;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::constructor_classifier;
use gandr_core_term::decoded_comp_reading;
use gandr_core_term::equal_type_reading;
use gandr_core_term::identity::Relation;
use gandr_core_term::instantiate_value_type_under;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::session::Step;
use gandr_core_term::shift_value;
use gandr_core_term::shift_value_type_under;
use gandr_core_term::strengthen_value_type;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_diagnostics::Checked;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::Naming;
use gandr_surface_diagnostics::PATHLESS;
use gandr_surface_diagnostics::Subject as DiagnosedSubject;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::ClauseBinder;
use gandr_surface_lowering::ClausePlace;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::DocumentationText;
use gandr_surface_lowering::InScope;
use gandr_surface_lowering::Insertion;
use gandr_surface_lowering::Labelled;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::PatternReading;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_lowering::described::DescribedRole;
use gandr_surface_lowering::documentation;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Scopes;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::WrittenName;
use gandr_surface_pretty::present_computation_line;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::Checking;
use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::JudgedClosure;
use crate::compose::Lowered;
use crate::compose::Lowering;
use crate::compose::LoweringCount;
use crate::compose::adapt;
use crate::compose::judge_lowering;
use crate::compose::lower_onto_closure;
use crate::compose::lower_parsed_unit;
use crate::compose::lower_unit_source;
use crate::evaluate::Evaluation;
use crate::typed::referent::Referents;

mod referent;

pub use crate::typed::referent::DeclaredHalf;
pub use crate::typed::referent::NameKind;
pub use crate::typed::referent::Referent;
pub use crate::typed::referent::referred;

quenchant_shape::reason_enum! {
    /// Why a position or a declaration has no type in the table.
    pub mod typing {
        /// The reason nothing is spelled.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No entry's span holds the position, or no declaration has the
            /// form's key.
            Untyped,
            /// The printer could not lay the type out at the page width.
            Unspelled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an entry carries no second type.
    pub mod checked_against {
        /// The reason only one type is spelled.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No outer judgement checked the term against a type spelled
            /// otherwise, or the entry is no term.
            Agreed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the table holds no refusal for a declaration.
    pub mod unrefused {
        /// The reason no refusal is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The table holds the declaration's type.
            Typed,
            /// No declaration has the key.
            Undeclared,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the table holds no refusal of the source as a whole.
    pub mod wholly {
        /// The reason no such refusal is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering read the source.
            Lowered,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a spelling has no reprint.
    pub mod reprinted {
        /// The reason the spelling was not printed again.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The spelling was not lowered: it was settled before any
            /// lowering, did not parse, or the lowering refused it.
            Unlowered,
            /// The printer could not lay the lowered node out.
            Unspelled,
            /// The read-back run did not settle or did not run to a value.
            Unrun,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a value is read back with no declaration's type.
    pub mod signed {
        /// The reason the value is read unsigned.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No run returned the value: a normal form, whose constructors
            /// carry its type.
            Unsigned,
        }
    }
}

/// What an entry of the table stands for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Subject
{
    /// A name binding the uses that resolve to it, spelled at their type.
    Binder,
    /// A term a judgement typed, spelled at its type.
    Term,
    /// A written type, spelled at its universe: a type the checker forms, or
    /// one a static function takes, lowered as a code and spelled at its
    /// universe or at the operator type that ends in one.
    Type,
}

/// Whether a written name binds there or uses what binds elsewhere.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Binding
{
    /// A use of a binder or of a declaration.
    Uses,
    /// A binder's own name.
    Binds,
}

/// Whether a term is read as a value or run as a computation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Polarity
{
    /// A value: a binder's, a constructor's, a thunk passed along.
    Value,
    /// A computation: a thunk forced where it is written, as a call forces
    /// the function it names.
    Computation,
}

/// How the table reads one span its source wrote a binder or a term at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Reading
{
    /// Whether a binder's name is written there.
    pub binding: Binding,
    /// Whether a term there is run as a computation.
    pub polarity: Polarity,
}

/// One node the source wrote, with the type a face shows for it.
///
/// # Specification
/// - requires: answered by [`TypeTable::at`].
/// - ensures: the span is the node's in the source the table was built from;
///   the type is spelled through [`present_type`].
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`TypeTable::at`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a term, a binder and a written type each carry their own
///   subject, span and spelling.
/// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypedSpan
{
    /// The bytes the node covers.
    span: ByteSpan,
    /// What the node is.
    subject: Subject,
    /// Whether the source wrote the node or the lowering inserted it.
    provenance: Provenance,
    /// The node's type: a term's own, a binder's uses', a type's universe.
    ty: Presentation,
    /// The type an outer judgement checked a term against, when spelled
    /// otherwise than its own.
    expected: Maybe<Presentation, checked_against::Absent>,
}

impl TypedSpan
{
    /// The bytes the node covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// What the node is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn subject(&self) -> Subject
    {
        self.subject
    }

    /// The node's type: a term's own, a binder's uses', a type's universe.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ty(&self) -> &Presentation
    {
        &self.ty
    }

    /// The type an outer judgement checked a term against, when spelled
    /// otherwise than its own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn expected(&self) -> Maybe<&Presentation, checked_against::Absent>
    {
        match self.expected {
            Maybe::Present(ref expected) => Maybe::Present(expected),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// What the table holds for a declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Declared
{
    /// The declaration's type: its signature, its body's synthesised type, or
    /// its data universe.
    Typed(Presentation),
    /// The lowering's refusal of the declaration, as text: no judgement
    /// reached it.
    Refused(String),
}

/// Which printed type of a table a read back reads: an entry's own, the type
/// an outer judgement checked the entry against, or a declaration's.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ReadSite
{
    /// The type an entry at this span answers with.
    Own(ByteSpan),
    /// The type an outer judgement checked the term at this span against,
    /// spelled otherwise than its own.
    CheckedAgainst(ByteSpan),
    /// The type of the declaration whose form has this key.
    Declared(NodeKey),
}

/// What reading one printed type back gave.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RoundTrip
{
    /// The printed type parses and lowers to the certificate the node
    /// carries.
    Equal,
    /// The printed type lowers to another certificate.
    Different,
    /// The printed type names a binder of the node's context: it reads back
    /// under that context alone, which a closed signature does not state.
    Open,
    /// The printed type holds a `?` the printer wrote where it cannot spell
    /// what the checker holds — an unknown type, a hole: no source spelling
    /// denotes it.
    Unknown,
    /// The printer could not lay the type out.
    Unspelled,
    /// The printed type does not parse as a signature's type.
    Unparsed,
    /// The lowering refused the printed type; the refusal, as text.
    Refused(String),
}

/// One printed type of a table and what reading it back gave.
///
/// # Specification
/// - requires: answered by [`TypeTable::read_back`].
/// - ensures: `spelled` is the type as a face prints it at `site`, and `trip`
///   what parsing and lowering that spelling gave against the type node the
///   table holds there.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`TypeTable::read_back`] carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TypeTable::read_back`].
/// - witness: `typed::tests::a_printed_type_reads_back_to_its_certificate`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadBack
{
    /// Where the type was printed.
    pub site: ReadSite,
    /// The type as printed.
    pub spelled: String,
    /// What reading it back gave.
    pub trip: RoundTrip,
    /// The type the spelling lowered to, printed again as the table prints:
    /// the printer is a fixed point exactly when this is the spelling.
    pub reprinted: Maybe<String, reprinted::Absent>,
}

/// One typed node as the table keeps it: the type nodes it is spelled at when
/// a reader asks.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Entry
{
    /// The bytes the node covers.
    span: ByteSpan,
    /// What the node is.
    subject: Subject,
    /// Whether the source wrote the node or the lowering inserted it.
    provenance: Provenance,
    /// The node's type: a term's first kept type, a binder's uses', a type's
    /// universe.
    ty: TypeNode,
    /// A term's last kept type, the type an outer judgement checked it
    /// against; [`Self::ty`] for any other entry.
    last: TypeNode,
    /// The binders the node's type is read under.
    standing: Standing,
}

/// Where a typed node stands: the declaration whose run first typed it, the
/// node itself, and the binders that typing was read under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Within
{
    /// The declaration, by the constant it admits.
    constant: ConstantIndex,
    /// The node.
    node: CoreNode,
    /// How many intuitionistic binders the run judged the node's type under:
    /// a node the term shares between places of other depths answers at its
    /// place under this many. None where the table keeps no typing of the
    /// node, a session endpoint's, which answers at its first place.
    depth: Option<BinderDepth>,
}

/// One judged term with the type its first and its last typing at the first
/// typing's depth gave it, the run position it was first judged at, and the
/// declaration and binder depth that first typing was read under.
type Kept = (
    TermNode,
    TypeNode,
    TypeNode,
    usize,
    (ConstantIndex, BinderDepth),
);

/// The binders an entry's type is read under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// None: the type is closed.
    Closed,
    /// Those around a node a declaration's run typed, named by walking the
    /// declaration's scopes.
    Judged(Within),
    /// Those of a context the lowering names: a described member's, as the
    /// description route records it, or a written label's.
    Named(NamedContext),
    /// Those around a node a declaration's run typed, then the binders a
    /// context the lowering names holds, innermost: the parts of a constructor
    /// pattern before a part whose field type names an earlier field.
    Parted(Within, NamedContext),
}

/// A context the lowering names, by its place in [`TypeTable::contexts`].
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamedContext(usize);

/// How many of a pattern's parts come before a part whose type stands under
/// them: none for a part typed outside its pattern.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Before(usize);

/// The pattern a part stands inside, with how many of that pattern's parts
/// before it the part's type stands under; none for a root pattern.
type Inside = Option<(PatternId, Before)>;

/// The parts of `pattern` that a part standing under `before` of them stands
/// under, in written order.
///
/// # Specification
/// trivial.
fn preceding(
    pattern: &Pattern,
    Before(count): Before,
) -> &[PatternId]
{
    match *pattern {
        Pattern::Constructor { ref fields, .. } => fields.get(.. count).unwrap_or_default(),
        Pattern::Pair(ref first, _) if count > 0_usize => core::slice::from_ref(first),
        Pattern::Pair(..)
        | Pattern::Injection(..)
        | Pattern::Wildcard
        | Pattern::Binder
        | Pattern::Unit
        | Pattern::Literal(_)
        | Pattern::Hole(_) => &[],
    }
}

/// The context an entry's type is spelled in: the names of the
/// intuitionistic binders around it, and of the capability scopes among
/// them, each outermost first, and the type each binder binds where the
/// table knows it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Context
{
    /// The binders' names; none where the source writes none.
    binders: Vec<Option<String>>,
    /// The regions' names, a capability scope's or a hold's, the first the
    /// outermost region.
    regions: Vec<Option<String>>,
    /// The type each binder binds, in the context of the binders before it;
    /// none where the table knows none.
    types: Vec<Option<ValueTypeId>>,
}

/// The binders a printed type naming them stands under, declared as the
/// parameters of a function the type is read back as the last parameter of.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Under
{
    /// Each binder as a parameter, `name : type, `, outermost first.
    parameters: String,
    /// The binders' names the parameters declare, and the types they bind.
    context: Context,
}

/// One printed type the read-back reads: where it was printed, the node it
/// was printed from and its spelling, its trip when it is settled before any
/// lowering, and the binders a type naming them stands under.
#[derive(Clone, Debug)]
struct Printed
{
    /// Where the type was printed.
    site: ReadSite,
    /// The node the type was printed from.
    node: TypeNode,
    /// The spelling, empty when the printer could not spell it.
    spelled: String,
    /// The trip, when it is settled before any lowering.
    settled: Option<RoundTrip>,
    /// The binders a type naming them stands under.
    under: Option<Under>,
}

/// Each pair of `named` with the label `text` writes at its span, and each
/// pair `reread` names, ascending by pair.
///
/// # Specification
/// trivial.
fn labelled<'names>(
    named: &[(ValueTypeId, ByteSpan)],
    text: SourceText<'names>,
    reread: &'names [(ValueTypeId, String)],
) -> Vec<(ValueTypeId, Name<'names>)>
{
    let text: &str = text.into();
    let mut labelled: Vec<(ValueTypeId, Name<'names>)> = named
        .iter()
        .filter_map(|&(pair, span)| {
            text.get(usize::from(span.start()) .. usize::from(span.end()))
                .map(|name| (pair, Name::from(name)))
        })
        .chain(
            reread
                .iter()
                .map(|&(pair, ref name)| (pair, Name::from(name.as_str()))),
        )
        .collect();
    labelled.sort_by_key(|&(pair, _)| pair);
    labelled
}

/// What a reprint's own lowering keeps beside the types it read, at their
/// images in the table's arena: the name each dependent arrow binds, the
/// labels each dependent pair was written with and the relation each type
/// was written as.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Read
{
    /// Each dependent arrow's image with the name it binds.
    arrows: Vec<(CompTypeId, String)>,
    /// Each dependent pair's image with the label its binder was written as.
    pairs: Vec<(ValueTypeId, String)>,
    /// Each dependent pair's image with the label its second was written as.
    seconds: Vec<(ValueTypeId, String)>,
    /// Each related type's image with the relation it was written as.
    relations: Vec<(ValueTypeId, Relation)>,
}

/// What the table keeps for a declaration: its type node, a refusal of it as
/// text, or its type node and the checker's refusal of it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Held
{
    /// The declaration's type node.
    Typed(TypeNode),
    /// A refusal, as text: the lowering's, or the checker's of a declaration
    /// the lowering gave no type.
    Refused(String),
    /// The declaration's type node, and the checker's refusal of the
    /// declaration, as text.
    Rejected
    {
        /// The declaration's type node.
        ty: TypeNode,
        /// The checker's refusal, as text.
        refusal: String,
    },
}

/// The direction the order chose for a written rule.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ChosenDirection
{
    /// The written left side rewrites to the written right.
    LeftToRight,
    /// The written right side rewrites to the written left.
    RightToLeft,
}

/// The type of every node of one source a face can point at, and of every
/// declaration.
///
/// # Specification
/// - requires: built by [`TypeTable::of`].
/// - ensures: the entries are in the order the typed run finished them, binders
///   and types after the terms; each declaration is keyed by each of its forms;
///   every type node lives in the table's arena, and the names are the source's
///   constants by admission position, each spelled by its path from the top
///   level.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`TypeTable::of`]
///   and [`TypeTable::at`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TypeTable::of`].
/// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeTable
{
    /// The typed nodes.
    entries: Vec<Entry>,
    /// Each declaration's type or refusal, by the key of each of its forms.
    declared: BTreeMap<NodeKey, Held>,
    /// The arena every type node lives in.
    arena: CoreArena,
    /// The name the printer writes for each constant, by admission position.
    names: Vec<String>,
    /// What the table keeps to name the binders an entry stands under.
    naming: Naming,
    /// The constructors of the source's data declarations, by family.
    families: Families,
    /// The names each described member's context binds, outermost first.
    contexts: Vec<Vec<String>>,
    /// Each oriented rule's span and the direction the order chose.
    orientations: Vec<(ByteSpan, ChosenDirection)>,
    /// The data signatures the typed run formed, by admission position: the
    /// words a path type reads as when a printed type is read back.
    signatures: BTreeMap<ConstantIndex, Arc<DataSignature>>,
    /// The type each term former opening a binder binds, by the former,
    /// ascending: a lambda's domain, a bind's returned value, a fixpoint's
    /// own thunk, a static lambda's domain, read off the first type the typed
    /// run kept for the former, or for a bind for its bound computation.
    opened: Vec<(CoreNode, ValueTypeId)>,
    /// The unit the source was lowered in, which a reading back lowers the
    /// source and its probe in again: the siblings an importer reads stand
    /// before it, its imports resolved to them.
    unit: Unit,
    /// Where the source's own text starts in the unit's.
    base: ByteOffset,
    /// Each written use the lowering resolved, with what it refers to.
    referents: Referents,
    /// Each span of the source's own text an entry for a binder or a term
    /// covers, with how the entries there read it, ascending.
    readings: Vec<(ByteSpan, Reading)>,
    /// The binders in scope at each offset of the unit's text the lowering
    /// read under one.
    in_scope: InScope,
    /// The lowering's refusal of the source as a whole, as it reads, when the
    /// lowering refused it: the table then holds nothing else.
    refused: Option<String>,
    /// The documentation each source of the unit writes of itself, its `//!`
    /// runs, by the source.
    documented: BTreeMap<SourceIndex, DocumentationText>,
}

/// The printer's root for `node`.
///
/// # Specification
/// trivial.
const fn root(node: TypeNode) -> CoreNode
{
    match node {
        TypeNode::Value(id) => CoreNode::ValueType(id),
        TypeNode::Computation(id) => CoreNode::CompType(id),
    }
}

/// What a term typed `first` first and `last` last stands for, and the last
/// type it is spelled against: a written type at `first` when it is a code no
/// check moved — its type a universe, or a static Π whose codomain is one,
/// and its last type the same in syntax — and a term otherwise.
///
/// # Specification
/// trivial.
fn term_subject(
    arena: &CoreArena,
    (first, last): (TypeNode, TypeNode),
) -> (Subject, TypeNode)
{
    let (TypeNode::Value(mut ty), TypeNode::Value(moved)) = (first, last)
    else {
        return (Subject::Term, last);
    };
    if gandr_core_term::equal_type_syntax(arena, ty, moved) != CertificateEquality::Equal {
        return (Subject::Term, last);
    }
    loop {
        match arena.value_type(ty) {
            Some(&ValueType::Universe { .. }) => return (Subject::Type, first),
            Some(&ValueType::StaticPi { codomain, .. }) => ty = codomain,
            Some(_) | None => return (Subject::Term, last),
        }
    }
}

/// `span` as the source starting at `base` measures it, when it lies there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `span` moved back by `base` bytes when it starts at or past
///   `base`; `None` before it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an importer's use types at its own offset and a sibling's
///   entries are not kept.
/// - witness: `typed::tests::an_imported_name_types_at_its_use`
#[spec(ensures: |ret| ret.is_none_or(|moved| {
    usize::from(moved.start()).saturating_add(usize::from(base)) == usize::from(span.start())
        && usize::from(moved.end()).saturating_add(usize::from(base)) == usize::from(span.end())
}))]
fn own(
    span: ByteSpan,
    base: ByteOffset,
) -> Option<ByteSpan>
{
    let start = usize::from(span.start()).checked_sub(usize::from(base))?;
    let end = usize::from(span.end()).checked_sub(usize::from(base))?;
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
}

/// Each type `module` writes from `base` on, with its origin and the sort of
/// the universe it lies in: the types a table answers at their universe.
///
/// A transport's written motive is a written type: the family it denotes. So
/// is a decode, the type a code written where a type is read denotes.
///
/// # Specification
/// - requires: `arena` holds `module`'s nodes.
/// - ensures: every value type and stand-in, then every computation type, then
///   every transport's motive the lowering wrote at or after `base`, written or
///   inserted as a decode, in the origin table's order.
/// - fails: never.
/// - panics: none.
/// - executable: none — a projection of the origin table, read back by the
///   table's universe entries.
///
/// # Adequacy
/// - hypothesis: L3 — a source writing a value type, a computation type and a
///   transport answers each at its universe; a type a model's header derives
///   from its signature, written by no one, answers nowhere.
/// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
/// - witness: `typed::tests::a_model_header_answers_no_term_its_signature_derives_477`
pub fn written_types(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    base: ByteOffset,
) -> Vec<(TypeNode, Origin, GroundSort)>
{
    let origins = module.origins();
    let value_types = origins
        .value_types()
        .iter()
        .chain(origins.stand_ins())
        .map(|&(id, origin)| (TypeNode::Value(id), origin, GroundSort::Value));
    let comp_types = origins
        .comp_types()
        .iter()
        .map(|&(id, origin)| (TypeNode::Computation(id), origin, GroundSort::Computation));
    let motives = origins.motives().iter().filter_map(|&(transport, origin)| {
        match arena.computation(transport) {
            Some(
                &(Computation::PathTransport { motive, .. } | Computation::Ride { motive, .. }),
            ) => Some((TypeNode::Value(motive), origin, GroundSort::Value)),
            _ => None,
        }
    });
    value_types
        .chain(comp_types)
        .chain(motives)
        .filter(|&(_, origin, _)| {
            origin.span().start() >= base
                && matches!(
                    origin.provenance(),
                    Provenance::Written | Provenance::Inserted(Insertion::Decode)
                )
        })
        .collect()
}

/// The types of `written` whose first formation a typed run keeps, each
/// once, ascending.
///
/// # Specification
/// trivial.
pub fn wanted_types(written: &[(TypeNode, Origin, GroundSort)]) -> Vec<TypeNode>
{
    let mut wanted: Vec<TypeNode> = written.iter().map(|&(node, ..)| node).collect();
    wanted.sort_unstable();
    wanted.dedup();
    wanted
}

/// What a table reads off a typed run of a module's declarations while the
/// run's context is live.
///
/// # Specification
/// - executable: none — a data type; [`TypeTable::assemble`] reads it.
pub struct TypedRun
{
    /// The types each declaration's run formed and judged, and its refusal.
    typed: TypedModule,
    /// The data signatures the run formed, by admission position.
    signatures: BTreeMap<ConstantIndex, Arc<DataSignature>>,
    /// The bodies a code constant unfolds to.
    definitions: CodeDefinitions,
    /// Each written type whose level was read, with its origin, the sort of
    /// its universe and that level.
    levels: Vec<(Origin, GroundSort, Level)>,
}

impl TypedRun
{
    /// What a table reads off the run `context` holds, which kept `typed`
    /// and the first formation of each type [`wanted_types`] names of
    /// `written`.
    ///
    /// Each written type answers at its universe: the level the typed run
    /// formed it at under the binders it was formed under, the first
    /// formation kept; a written type no kept formation reached — formed by a
    /// rule that forms it outside a formation goal — at the level it reads
    /// closed; a type at neither is not answered.
    ///
    /// # Specification
    /// - requires: `context` judged the declarations `typed` keeps, keeping the
    ///   formations [`wanted_types`] names of `written`.
    /// - ensures: the run's data signatures and definitions, and the level of
    ///   each written type whose level was read, in `written`'s order.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — a read of the context, compared whole by the
    ///   witness of [`TypeTable::assemble`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TypeTable::assemble`].
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    pub fn read(
        context: &CheckingContext<'_>,
        typed: TypedModule,
        written: Vec<(TypeNode, Origin, GroundSort)>,
    ) -> Self
    {
        let signatures = context.data_signatures().clone();
        let definitions = context.definitions().clone();
        // Each wanted type is formed at most once, so the formations sorted by
        // type find a written type's own by search; the stable sort keeps the
        // first should a type appear twice.
        let mut formed: Vec<&Formed> = typed.typings().values().flat_map(Typings::formed).collect();
        formed.sort_by_key(|formation| formation.ty);
        formed.dedup_by_key(|formation| formation.ty);
        let mut levels = Vec::new();
        for (node, origin, sort) in written {
            let level = match formed.binary_search_by_key(&node, |formation| formation.ty) {
                Ok(at) => match formed.get(at) {
                    Some(formation) => formation.level.clone(),
                    None => continue,
                },
                Err(_) => match level_of(context, node) {
                    Ok(level) => level,
                    Err(_) => continue,
                },
            };
            levels.push((origin, sort, level));
        }
        Self {
            typed,
            signatures,
            definitions,
            levels,
        }
    }
}

impl TypeTable
{
    /// Type every node of `source` a face can point at.
    ///
    /// # Specification
    /// - requires: `grammar` is the checked grammar the source is parsed under.
    /// - ensures: the source is parsed, lowered and judged in the checker's
    ///   typed run; each term the run typed and the origin table places is an
    ///   entry at its span, at the first type the run kept for it and the last,
    ///   and a written type when the term is a code — its type a universe or a
    ///   static Π ending in one — that no check against another type moved,
    ///   save a term of a model's derived type, which the source writes
    ///   nowhere; each binder the origin table records for a typed use is one
    ///   entry at the binder's span, at that use's type; each written value or
    ///   computation type whose level the checker reads is an entry at its
    ///   universe; each declaration is keyed by each form key it carries, at
    ///   its declared type, its body's synthesised type, its data universe, or
    ///   a sealed abstract type's kind, or holding the lowering's refusal of it
    ///   as text, a `data` family's operations leaving the family's key its
    ///   own; each node a `theory` block or a `data` family's constructors,
    ///   operations and rules write is an entry at the type its member states
    ///   ([`LoweredModule::described_types`]), read under the names of the
    ///   members before it. A source the lowering refuses whole types nothing.
    /// - provides: what a face answers a reader pointing into the source with.
    /// - fails: [`ComposeFault::Parse`] when the parser cannot commit its tree;
    ///   [`ComposeFault::Lowering`] for a lowering engine fault.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ComposeFault::Parse`]: the tree could not be committed.
    /// - [`ComposeFault::Lowering`]: the lowering faulted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function with a parameter used in its body, a
    ///   signature and its definition, a synthesised definition, a data
    ///   declaration and a mismatched body separate the term, binder, type and
    ///   declaration entries and the expected type; a theory's members and a
    ///   data family with an operation answer at their own types; a type
    ///   written where a static function takes one answers as a written type; a
    ///   model header's theory answers no term its derived types hold.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_type_under_a_static_binder_answers_as_a_written_type`
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
    /// - witness: `typed::tests::both_halves_of_a_declaration_find_its_type`
    /// - witness: `typed::tests::a_theory_member_answers_under_the_sorts_before_it`
    /// - witness: `typed::tests::a_data_family_is_keyed_at_its_own_type_past_its_operations`
    /// - witness: `typed::tests::a_model_header_answers_no_term_its_signature_derives_477`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|table| table.entries.iter().all(|entry|
        usize::from(entry.span.end()) <= <&str>::from(source).len()
            && (entry.subject == Subject::Term || entry.last == entry.ty)))
        || ret.is_err())]
    #[inline]
    pub fn of<'source>(
        grammar: &Pbg,
        source: SourceText<'source>,
    ) -> Result<Self, ComposeFault<'source>>
    {
        Self::of_unit(grammar, source, &Unit::single(), ByteOffset::from(0_usize))
    }

    /// [`of`](Self::of) over the tree `parsed` committed for a source alone.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`of_parsed_unit`](Self::of_parsed_unit).
    #[inline]
    pub fn of_parsed<'source>(
        grammar: &Pbg,
        parsed: ParseResult<'source>,
    ) -> Result<Self, ComposeFault<'source>>
    {
        Self::of_parsed_unit(grammar, parsed, &Unit::single(), ByteOffset::from(0_usize))
    }

    /// Type every node of the source starting at `base` in `source`, the text
    /// `unit` lays out: [`of`](Self::of) over a source lowered beside the
    /// siblings it imports.
    ///
    /// # Specification
    /// - requires: `grammar` is the checked grammar; `source` is the text
    ///   `unit` lays out, and `base` starts its last source.
    /// - ensures: as [`of`](Self::of) over the whole unit, keeping the entries
    ///   and rule orientations at or past `base`, each moved back by `base`
    ///   bytes, so the table answers offsets into the last source's own text;
    ///   the last source's declarations are keyed by their forms' keys in that
    ///   source's own tree, which no offset moves, and a sibling's — even one
    ///   writing the same form byte for byte (#596) — are not kept. A
    ///   declaration refused for binding again a name an unqualified import
    ///   binds answers at none of its sites (#677). The table keeps the unit,
    ///   which every reading back lowers in again, and the documentation each
    ///   source of it writes of itself, by the source. Unchanged at offset zero
    ///   over [`Unit::single`].
    /// - provides: what an editor answers inside a document that imports a
    ///   sibling: an imported name types as its declaration does.
    /// - fails: as [`of`](Self::of).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`of`](Self::of).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name a sibling declares types at its use in the
    ///   importer, at the importer's own offset; a declaration the import
    ///   shadows answers nowhere and the importer's others still read back.
    /// - witness: `typed::tests::an_imported_name_types_at_its_use`
    /// - witness: `typed::tests::a_declaration_refused_as_shadowing_answers_at_no_site_677`
    /// - witness: `typed::tests::the_table_keeps_each_source_s_own_documentation_1365`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|table| table.entries.iter().all(|entry|
        usize::from(entry.span.end())
            <= <&str>::from(source).len().saturating_sub(usize::from(base))))
        || ret.is_err())]
    #[inline]
    pub fn of_unit<'source>(
        grammar: &Pbg,
        source: SourceText<'source>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Result<Self, ComposeFault<'source>>
    {
        let parsed = parse(grammar, source).map_err(ComposeFault::Parse)?;
        Self::of_parsed_unit(grammar, parsed, unit, base)
    }

    /// [`of_unit`](Self::of_unit) over the tree `parsed` committed for the
    /// text `unit` lays out: a face that holds a parse of the text — an
    /// editor's session, whose form store takes up every form it molded
    /// before — types it without parsing it again.
    ///
    /// # Specification
    /// - requires: `grammar` is the checked grammar `parsed` was committed
    ///   under, over the text `unit` lays out, its last source starting at
    ///   `base`.
    /// - ensures: what [`of_unit`](Self::of_unit) ensures of `parsed`'s source.
    /// - provides: the hover table of a document, typed over the parse its
    ///   session's form store answers.
    /// - fails: [`ComposeFault::Lowering`] for a lowering engine fault.
    /// - panics: none.
    /// - executable: none — [`of_unit`](Self::of_unit) states the clause and
    ///   types through this.
    ///
    /// # Errors
    /// [`ComposeFault::Lowering`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`of_unit`](Self::of_unit), every witness of which
    ///   types through this.
    /// - witness: `typed::tests::an_imported_name_types_at_its_use`
    #[inline]
    pub fn of_parsed_unit<'source>(
        grammar: &Pbg,
        parsed: ParseResult<'source>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Result<Self, ComposeFault<'source>>
    {
        let source = parsed.tree().source();
        let lowering = lower_parsed_unit(
            grammar,
            parsed,
            unit,
            &mut LoweringCount::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )?;
        Ok(Self::typed(source, lowering, Checking::Whole, unit, base))
    }

    /// [`of_parsed_unit`](Self::of_parsed_unit) over the tree `parsed`
    /// committed for a document laid after `judged`'s closure: the document
    /// lowered after the closure's judged arena and its own declarations
    /// typed on the checker's state after the closure's.
    ///
    /// # Specification
    /// - requires: as [`of_parsed_unit`](Self::of_parsed_unit), `parsed` laid
    ///   after `judged`'s closure's tree.
    /// - ensures: the module [`lower_onto_closure`] lowers, typed as
    ///   [`of_parsed_unit`](Self::of_parsed_unit) types its source, the typed
    ///   run resumed on the checker's state after the closure's declarations
    ///   and run over the document's own when they lead the module, and over
    ///   every declaration otherwise.
    /// - provides: the hover table of a document that imports a sibling, typed
    ///   in the document's size rather than its closure's.
    /// - fails: as [`of_parsed_unit`](Self::of_parsed_unit).
    /// - panics: none.
    /// - executable: none — the clause names a typing no argument carries; the
    ///   witness types every node of a document both ways and compares.
    ///
    /// # Errors
    /// As [`of_parsed_unit`](Self::of_parsed_unit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document typed after its judged closure answers
    ///   every position as one typed whole does.
    /// - witness: `typed::tests::a_document_typed_after_its_closure_types_as_one_typed_whole_776`
    #[inline]
    pub fn of_parsed_after<'held>(
        judged: &'held JudgedClosure,
        parsed: ParseResult<'held>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Result<Self, ComposeFault<'held>>
    {
        let source = parsed.tree().source();
        let (lowering, checking) = lower_onto_closure(
            judged,
            judged.arena(),
            parsed,
            unit,
            &mut LoweringCount::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )?;
        Ok(Self::typed(source, lowering, checking, unit, base))
    }

    /// The table of `lowering`, the source `unit` lays out with its last
    /// source starting at `base`, its declarations typed as `checking` says.
    ///
    /// # Specification
    /// - requires: `lowering` lowers `source` over `unit`.
    /// - ensures: as [`of_unit`](Self::of_unit) over `lowering`; after a
    ///   closure whose declarations lead the module, the typed run resumed on
    ///   the checker's state after them and run over the rest.
    /// - fails: never; a source refused whole types nothing.
    /// - panics: none.
    /// - executable: none — as [`of_unit`](Self::of_unit), which types through
    ///   this.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`of_unit`](Self::of_unit) and
    ///   [`of_parsed_after`](Self::of_parsed_after); a constructor's stated
    ///   index answers under its frame and a function between two frames under
    ///   its own binders; a term after a declaration refused as shadowing still
    ///   answers.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_document_typed_after_its_closure_types_as_one_typed_whole_776`
    /// - witness: `typed::tests::only_a_stated_index_answers_under_its_frame_931`
    /// - witness: `typed::tests::a_term_after_a_declaration_refused_as_shadowing_still_answers_677`
    fn typed(
        source: SourceText<'_>,
        lowering: Lowering<'_>,
        checking: Checking<'_>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Self
    {
        let refused = lowering.refused().map(|&refusal| {
            diagnose(
                Path::new(PATHLESS),
                source,
                DiagnosedSubject::Source(refusal),
            )
            .message
            .text
        });
        let Lowered::Module { module, mut arena } = lowering.into_lowered()
        else {
            return Self {
                refused,
                ..Self::default()
            };
        };
        let declarations = adapt(&module);
        let written = written_types(&module, &arena, base);
        let wanted = wanted_types(&written);
        let after = match checking {
            Checking::After(closure) => closure.led(&declarations),
            Checking::Whole => None,
        };
        let run = {
            let (mut context, own_declarations) = match after {
                Some((checkpoint, closure)) => (
                    CheckingContext::resume(&mut arena, checkpoint.clone()),
                    declarations.get(closure.len() ..).unwrap_or_default(),
                ),
                None => (
                    CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
                    declarations.as_slice(),
                ),
            };
            context.keep_formations(Formations::Firsts(wanted));
            let typed = type_module(&mut context, own_declarations);
            TypedRun::read(&context, typed, written)
        };
        Self::assemble(source, (module, arena), run, (unit, base))
    }

    /// The table of `module`, the source `unit` lays out with its last source
    /// starting at `base`, lowered into `arena`, from what `run` read off the
    /// typed run of its declarations.
    ///
    /// # Specification
    /// - requires: `module` lowers `source` over `unit` into `arena`; `run` was
    ///   read by [`TypedRun::read`] off a typed run of `module`'s declarations
    ///   over `arena`, every declaration after a closure leading them, keeping
    ///   the formations [`wanted_types`] names.
    /// - ensures: the table [`typed`](Self::typed) builds of a run of `module`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`of_unit`](Self::of_unit), which types through
    ///   this.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table assembled from a judgement's typed run is the
    ///   table [`of_unit`](Self::of_unit) builds of the same source; a term
    ///   checked against another type keeps both; a term under a constructor's
    ///   stated index answers under its frame; a run's binder answers at what
    ///   its computation returns; a declaration refused as shadowing answers
    ///   nowhere inside it while a term after it does; both halves of a
    ///   declaration find its type.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `tests::corpus::a_judgement_s_table_answers_as_the_table_typed_alone_1521`
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
    /// - witness: `typed::tests::only_a_stated_index_answers_under_its_frame_931`
    /// - witness: `typed::tests::a_run_binder_answers_at_what_its_computation_returns_298`
    /// - witness: `typed::tests::a_declaration_refused_as_shadowing_answers_at_no_site_677`
    /// - witness: `typed::tests::a_term_after_a_declaration_refused_as_shadowing_still_answers_677`
    /// - witness: `typed::tests::both_halves_of_a_declaration_find_its_type`
    pub(crate) fn assemble(
        source: SourceText<'_>,
        (module, mut arena): (LoweredModule<'_>, CoreArena),
        run: TypedRun,
        (unit, base): (&Unit, ByteOffset),
    ) -> Self
    {
        let TypedRun {
            typed,
            signatures,
            definitions,
            levels,
        } = run;
        let origins = module.origins();
        let universes: Vec<(Origin, TypeNode)> = levels
            .into_iter()
            .map(|(origin, sort, level)| {
                let universe = arena.value_type_universe(Sort::Ground(sort), level);
                (origin, TypeNode::Value(universe))
            })
            .collect();
        // Each described member's written nodes at what the member states,
        // minted past the typed run, which reads none of them.
        let described = module.described_types(&mut arena);
        // Each term's first and last type, when its last was kept, and the
        // declaration whose run first typed it: every typing in the order
        // kept, grouped by term with a sort, each group's first and last read
        // off its ends. A later typing under other binders than the first's —
        // a result type's term judged again as a case's motive, under the
        // case's binders — is no check of the term in its own context, and
        // its type reads past the binders the term's standing names (#551),
        // so it moves the term's place in the order but never its last type.
        let mut judged: Vec<(TermNode, usize, TypeNode, BinderDepth, ConstantIndex)> = typed
            .typings()
            .iter()
            .flat_map(|(&constant, typings)| {
                typings
                    .typings()
                    .iter()
                    .map(move |typing| (constant, typing))
            })
            .enumerate()
            .map(|(finished, (constant, typing))| {
                (typing.term, finished, typing.ty, typing.depth, constant)
            })
            .collect();
        judged.sort_unstable_by_key(|&(term, finished, ..)| (term, finished));
        // The declaration beside the binders its first typing was read under.
        let mut kept: Vec<Kept> = Vec::new();
        let mut first_depth = BinderDepth::default();
        for (term, finished, ty, depth, constant) in judged {
            match kept.last_mut() {
                Some(&mut (held, _, ref mut last, ref mut at, _)) if held == term => {
                    if depth == first_depth {
                        *last = ty;
                    }
                    *at = finished;
                },
                Some(_) | None => {
                    first_depth = depth;
                    kept.push((term, ty, ty, finished, (constant, depth)));
                },
            }
        }
        let first_of = |term: TermNode| {
            kept.binary_search_by_key(&term, |&(held, ..)| held)
                .ok()
                .and_then(|at| kept.get(at))
                .map(|&(_, first, _, _, judged)| (first, judged))
        };
        let first_type = |term: TermNode| first_of(term).map(|(first, _)| first);
        // Each binder a term former opens, at the type the first judgement of
        // the former, or of a bind's bound computation, states it binds.
        let mut opened: Vec<(CoreNode, ValueTypeId)> = Vec::new();
        for &(term, first, ..) in &kept {
            let bound = match (term, first) {
                (TermNode::Computation(id), TypeNode::Computation(ty)) => {
                    match arena.computation(id) {
                        Some(&Computation::Lambda(_)) => match arena.comp_type(ty) {
                            Some(
                                &(CompType::Pi { domain, .. } | CompType::Arrow { domain, .. }),
                            ) => Some(domain),
                            Some(_) | None => None,
                        },
                        Some(&Computation::Fixpoint { .. }) => Some(arena.value_type_thunk(ty)),
                        Some(&Computation::Bind(bound, _)) => {
                            match first_type(TermNode::Computation(bound)) {
                                Some(TypeNode::Computation(returned)) => {
                                    match arena.comp_type(returned) {
                                        Some(&CompType::Returner { result, .. }) => Some(result),
                                        Some(_) | None => None,
                                    }
                                },
                                Some(TypeNode::Value(_)) | None => None,
                            }
                        },
                        Some(_) | None => None,
                    }
                },
                (TermNode::Value(id), TypeNode::Value(ty)) => {
                    match (arena.value(id), arena.value_type(ty)) {
                        (
                            Some(&Value::StaticLambda(_)),
                            Some(&ValueType::StaticPi { domain, .. }),
                        ) => Some(domain),
                        (Some(_) | None, Some(_) | None) => None,
                    }
                },
                (TermNode::Computation(_), TypeNode::Value(_))
                | (TermNode::Value(_), TypeNode::Computation(_)) => None,
            };
            if let Some(ty) = bound {
                let node = match term {
                    TermNode::Value(id) => CoreNode::Value(id),
                    TermNode::Computation(id) => CoreNode::Computation(id),
                };
                opened.push((node, ty));
            }
        }
        opened.sort_by_key(|&(node, _)| node);
        // Each action's endpoint at the first session type a run found it
        // standing at, and the declaration whose run found it.
        let mut endpoints: Vec<(TermNode, TypeNode, ConstantIndex)> = typed
            .typings()
            .iter()
            .flat_map(|(&constant, typings)| {
                typings
                    .endpoints()
                    .iter()
                    .map(move |standing| (standing.term, standing.ty, constant))
            })
            .collect();
        endpoints.sort_by_key(|&(term, ..)| term);
        endpoints.dedup_by_key(|&mut (term, ..)| term);
        let names = constant_names(&module);
        let mut order: Vec<&Kept> = kept.iter().collect();
        order.sort_unstable_by_key(|&&(_, _, _, at, _)| at);
        let mut entries = Vec::with_capacity(order.len());
        for &(term, first, last, _, (constant, depth)) in order {
            let (origin, node) = match term {
                TermNode::Value(id) => (origins.value(id), CoreNode::Value(id)),
                TermNode::Computation(id) => (origins.computation(id), CoreNode::Computation(id)),
            };
            // A model's derived type is located at the signature its header
            // names, which writes the name and nothing the type holds, so no
            // term in it answers for those bytes (#477); nor does a term of
            // the record a relation between types abbreviates, located at the
            // relation, which writes the two types and nothing the record
            // holds, or a term of the words a data declaration's loops
            // present, located at the declaration; nor does a term of the
            // access a method call is, below the call, located at the call; nor
            // does a term of the bind a typed lambda parameter is read through,
            // located at the lambda; nor does a term of the law or the proof a
            // derived rule mints, located at the statement's name.
            if let Maybe::Present(origin) = origin
                && !matches!(
                    origin.provenance(),
                    Provenance::Inserted(
                        Insertion::Model
                            | Insertion::Relation
                            | Insertion::Words
                            | Insertion::Method
                            | Insertion::Parameter
                            | Insertion::Derived
                    )
                )
            {
                let (subject, last) = term_subject(&arena, (first, last));
                entries.push(Entry {
                    span: origin.span(),
                    subject,
                    provenance: origin.provenance(),
                    ty: first,
                    last,
                    standing: Standing::Judged(Within {
                        constant,
                        node,
                        depth: Some(depth),
                    }),
                });
            }
        }
        let mut binders = BTreeSet::new();
        for &(variable, binder) in origins.bindings() {
            if let Some((first, (constant, depth))) = first_of(TermNode::Value(variable))
                && binders.insert(binder)
            {
                entries.push(Entry {
                    span: binder,
                    subject: Subject::Binder,
                    provenance: Provenance::Written,
                    ty: first,
                    last: first,
                    standing: Standing::Judged(Within {
                        constant,
                        node: CoreNode::Value(variable),
                        depth: Some(depth),
                    }),
                });
            }
        }
        // Each pattern at the type its place in the scrutinee's gives it: the
        // scrutinee is judged before the arms, so a match whose body the run
        // refused still types its patterns. The scrutinee is the value the
        // match's record names, or, where the run judged a copy of the match
        // the lowering rebuilt and not that value, the value written at the
        // scrutinee's node. A binder some use already answers is not answered
        // twice.
        let typed_at = |value: ValueId| match first_of(TermNode::Value(value)) {
            Some((TypeNode::Value(ty), (constant, depth))) => Some(Scrutinised {
                ty,
                within: Within {
                    constant,
                    node: CoreNode::Value(value),
                    depth: Some(depth),
                },
            }),
            Some((TypeNode::Computation(_), _)) | None => None,
        };
        let mut scrutinised: BTreeMap<NodeIndex, Scrutinised> = BTreeMap::new();
        for (_, case) in origins.cases() {
            if let Maybe::Present(value) = case.scrutinised
                && let Some(typed) = typed_at(value)
            {
                let _first = scrutinised.entry(case.scrutinee).or_insert(typed);
            }
        }
        let unjudged: BTreeSet<NodeIndex> = origins
            .cases()
            .map(|(_, case)| case.scrutinee)
            .filter(|node| !scrutinised.contains_key(node))
            .collect();
        if !unjudged.is_empty() {
            for &(value, origin) in origins.values() {
                if origin.provenance() == Provenance::Written
                    && unjudged.contains(&origin.node())
                    && !scrutinised.contains_key(&origin.node())
                    && let Some(typed) = typed_at(value)
                {
                    let _first = scrutinised.insert(origin.node(), typed);
                }
            }
        }
        let mut contexts: Vec<Vec<String>> = described
            .contexts
            .iter()
            .map(|names| {
                names
                    .iter()
                    .map(|name| String::from(name.as_ref()))
                    .collect()
            })
            .collect();
        // An index a data constructor's result states is judged under the
        // family's parameters and the constructor's fields, which no term of
        // the declaration binds: every term written in it answers under the
        // names the lowering framed it with.
        for &(framed, ref names) in origins.framed() {
            let named = NamedContext(contexts.len());
            contexts.push(names.clone());
            for entry in &mut entries {
                if matches!(entry.standing, Standing::Judged(_))
                    && entry.span.start() >= framed.start()
                    && entry.span.end() <= framed.end()
                {
                    entry.standing = Standing::Named(named);
                }
            }
        }
        // A part whose type names the parts before it answers under them, by
        // the names its pattern writes for them.
        let text = <&str>::from(source);
        let mut constructed = Vec::new();
        for (span, ty, within, earlier) in matched(
            &module,
            &mut arena,
            &definitions,
            &scrutinised,
            &mut constructed,
        ) {
            if binders.contains(&span) {
                continue;
            }
            let standing = if earlier.is_empty() {
                Standing::Judged(within)
            }
            else {
                let Some(names) = earlier
                    .iter()
                    .map(|part| {
                        text.get(usize::from(part.start()) .. usize::from(part.end()))
                            .map(String::from)
                    })
                    .collect::<Option<Vec<String>>>()
                else {
                    continue;
                };
                let named = NamedContext(contexts.len());
                contexts.push(names);
                Standing::Parted(within, named)
            };
            let _fresh = binders.insert(span);
            entries.push(Entry {
                span,
                subject: Subject::Binder,
                provenance: Provenance::Written,
                ty: TypeNode::Value(ty),
                last: TypeNode::Value(ty),
                standing,
            });
        }
        // Each binder a capability scope's clauses write, at the type the
        // scope's first judgement binds it at: the result at what the subject
        // returns, a payload at its operation's payload, and a continuation at
        // the stack from the operation's reply, under the answer's effects, to
        // the answer. A binder some use already answers is not answered twice.
        for &((scope, clause), origin) in origins.clause_binders() {
            let span = origin.span();
            if binders.contains(&span) {
                continue;
            }
            let Some((TypeNode::Computation(answer), (constant, depth))) =
                first_of(TermNode::Computation(scope))
            else {
                continue;
            };
            let Some(&Computation::Scope {
                ref signature,
                subject,
                ref clauses,
                ..
            }) = arena.computation(scope)
            else {
                continue;
            };
            let operation = |place: ClausePlace| {
                let written = clauses.get(usize::from(place))?;
                match signature.operation(&written.operation) {
                    Maybe::Present(operation) => Some((operation.payload, operation.reply)),
                    Maybe::Absent(_) => None,
                }
            };
            let ty = match clause {
                ClauseBinder::Result => match first_type(TermNode::Computation(subject)) {
                    Some(TypeNode::Computation(returned)) => match arena.comp_type(returned) {
                        Some(&CompType::Returner { result, .. }) => Some(result),
                        Some(_) | None => None,
                    },
                    Some(TypeNode::Value(_)) | None => None,
                },
                ClauseBinder::Payload(place) => operation(place).map(|(payload, _)| payload),
                ClauseBinder::Continuation(place) => {
                    let replied = operation(place).map(|(_, reply)| reply);
                    let effects = match arena.comp_type(answer) {
                        Some(&CompType::Returner { ref effects, .. }) => Some(effects.clone()),
                        Some(_) | None => None,
                    };
                    replied.zip(effects).map(|(reply, effects)| {
                        let input = arena.comp_type_returner_with_effects(reply, effects);
                        arena.value_type_stack(input, answer)
                    })
                },
            };
            let Some(ty) = ty
            else {
                continue;
            };
            let _fresh = binders.insert(span);
            entries.push(Entry {
                span,
                subject: Subject::Binder,
                provenance: Provenance::Written,
                ty: TypeNode::Value(ty),
                last: TypeNode::Value(ty),
                standing: Standing::Judged(Within {
                    constant,
                    node: CoreNode::Computation(scope),
                    depth: Some(depth),
                }),
            });
        }
        // Each parameter a lambda binds and no use answers, at the domain the
        // lambda's first judgement states it binds, so a parameter nothing
        // reads answers at its own type rather than at the lambda that opens
        // it, written at the same name.
        for &(opener, name) in origins.binders() {
            let span = name.span();
            if name.provenance() != Provenance::Written
                || binders.contains(&span)
                || !matches!(arena.computation(opener), Some(&Computation::Lambda(_)))
            {
                continue;
            }
            let node = CoreNode::Computation(opener);
            let Some(&(_, domain)) = opened
                .binary_search_by_key(&node, |&(held, _)| held)
                .ok()
                .and_then(|at| opened.get(at))
            else {
                continue;
            };
            let Some((_, (constant, depth))) = first_of(TermNode::Computation(opener))
            else {
                continue;
            };
            let _fresh = binders.insert(span);
            entries.push(Entry {
                span,
                subject: Subject::Binder,
                provenance: Provenance::Written,
                ty: TypeNode::Value(domain),
                last: TypeNode::Value(domain),
                standing: Standing::Judged(Within {
                    constant,
                    node,
                    depth: Some(depth),
                }),
            });
        }
        // What each written computation returns, read at the first judgement
        // the run finished of a computation written there: a `run` binder
        // answers at what its bound computation returns, wherever a rewrite
        // of its block moved that computation (#298), and a computation judged
        // at a decode — `force m` with `m` at `+U (T(A))` — returns what the
        // decode reads as.
        let mut returned: BTreeMap<NodeIndex, (usize, ValueTypeId, Within)> = BTreeMap::new();
        for &(term, first, _, at, (constant, depth)) in &kept {
            let (TermNode::Computation(id), TypeNode::Computation(ty)) = (term, first)
            else {
                continue;
            };
            let ty = match arena.comp_type(ty) {
                Some(&CompType::Element { .. }) => decoded_comp_reading(&mut arena, ty),
                Some(_) | None => ty,
            };
            let Some(&CompType::Returner { result, .. }) = arena.comp_type(ty)
            else {
                continue;
            };
            let Maybe::Present(origin) = origins.computation(id)
            else {
                continue;
            };
            if origin.provenance() != Provenance::Written {
                continue;
            }
            let judged = (at, result, Within {
                constant,
                node: CoreNode::Computation(id),
                depth: Some(depth),
            });
            let _held = returned
                .entry(origin.node())
                .and_modify(|held| {
                    if at < held.0 {
                        *held = judged;
                    }
                })
                .or_insert(judged);
        }
        // A label answers at what it names: a field's or a binder's type,
        // read under the binders its entry is, or a record field's term at
        // its type. A binder some use already answers is not answered twice.
        for label in origins.labels() {
            if binders.contains(&label.span) {
                continue;
            }
            let (ty, standing) = match label.labelled {
                Labelled::ValueType { ty, ref context } => {
                    let named = NamedContext(contexts.len());
                    contexts.push(context.clone());
                    (TypeNode::Value(ty), Standing::Named(named))
                },
                Labelled::CompType { ty, ref context } => {
                    let named = NamedContext(contexts.len());
                    contexts.push(context.clone());
                    (TypeNode::Computation(ty), Standing::Named(named))
                },
                Labelled::Value(value) => {
                    let Some((first, (constant, depth))) = first_of(TermNode::Value(value))
                    else {
                        continue;
                    };
                    (
                        first,
                        Standing::Judged(Within {
                            constant,
                            node: CoreNode::Value(value),
                            depth: Some(depth),
                        }),
                    )
                },
                Labelled::Endpoint(action) => {
                    let Some(&(_, ty, constant)) = endpoints
                        .binary_search_by_key(&TermNode::Computation(action), |&(term, ..)| term)
                        .ok()
                        .and_then(|at| endpoints.get(at))
                    else {
                        continue;
                    };
                    (
                        ty,
                        Standing::Judged(Within {
                            constant,
                            node: CoreNode::Computation(action),
                            depth: None,
                        }),
                    )
                },
                // An offer arm's label answers at the session its endpoint
                // continues as in that arm (#298): the branch it names of the
                // offer the endpoint stands at.
                Labelled::Branch { action, ref label } => {
                    let Some(&(_, TypeNode::Value(offered), constant)) = endpoints
                        .binary_search_by_key(&TermNode::Computation(action), |&(term, ..)| term)
                        .ok()
                        .and_then(|at| endpoints.get(at))
                    else {
                        continue;
                    };
                    let Some(&ValueType::Session(ref session)) = arena.value_type(offered)
                    else {
                        continue;
                    };
                    let Ok(Step::Offer(branches)) = session.step()
                    else {
                        continue;
                    };
                    let Ok(Maybe::Present(next)) = branches.get(label)
                    else {
                        continue;
                    };
                    (
                        TypeNode::Value(arena.value_type_session(next)),
                        Standing::Judged(Within {
                            constant,
                            node: CoreNode::Computation(action),
                            depth: None,
                        }),
                    )
                },
                Labelled::Bound(node) => {
                    let Some(&(_, result, within)) = returned.get(&node)
                    else {
                        continue;
                    };
                    (TypeNode::Value(result), Standing::Judged(within))
                },
            };
            let _first = binders.insert(label.span);
            entries.push(Entry {
                span: label.span,
                subject: Subject::Binder,
                provenance: Provenance::Written,
                ty,
                last: ty,
                standing,
            });
        }
        for (origin, universe) in universes {
            entries.push(Entry {
                span: origin.span(),
                subject: Subject::Type,
                provenance: origin.provenance(),
                ty: universe,
                last: universe,
                standing: Standing::Closed,
            });
        }
        // A description a `ua` names is no core node: it answers at the
        // universe the statement's path lies in, the carrier of its type.
        for &(statement, named) in origins.sides() {
            let Some(TypeNode::Value(path)) = first_type(TermNode::Value(statement))
            else {
                continue;
            };
            let Some(&ValueType::Path { carrier, .. }) = arena.value_type(path)
            else {
                continue;
            };
            for origin in named {
                entries.push(Entry {
                    span: origin.span(),
                    subject: Subject::Type,
                    provenance: origin.provenance(),
                    ty: TypeNode::Value(carrier),
                    last: TypeNode::Value(carrier),
                    standing: Standing::Closed,
                });
            }
        }
        for entry in described.entries {
            let ty = TypeNode::Value(entry.ty);
            entries.push(Entry {
                span: entry.span,
                subject: match entry.role {
                    DescribedRole::Name => Subject::Binder,
                    DescribedRole::Term => Subject::Term,
                    DescribedRole::Type => Subject::Type,
                },
                provenance: Provenance::Written,
                ty,
                last: ty,
                standing: Standing::Named(NamedContext(usize::from(entry.context))),
            });
        }
        // A declaration refused for binding again a name an unqualified import
        // binds answers at none of its sites (#677): every name it writes reads
        // as the import's, so a type naming its own family would print a
        // spelling that reads back as the type it hides.
        let hidden: Vec<ByteSpan> = module
            .declarations()
            .iter()
            .filter(|declaration| {
                matches!(
                    declaration.outcome(),
                    DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { .. })
                )
            })
            .filter_map(
                |declaration| match origins.declaration(declaration.origin()) {
                    Maybe::Present(origin) => Some(origin.span()),
                    Maybe::Absent(_) => None,
                },
            )
            .collect();
        entries.retain(|entry| {
            !hidden
                .iter()
                .any(|form| form.start() <= entry.span.start() && entry.span.end() <= form.end())
        });
        let own_source = unit.source_at(base);
        let mut declared = BTreeMap::new();
        for declaration in module.declarations() {
            // A `data` family's operation and the words of its loops are
            // declared from the family's form and have no form of their own:
            // the family's key is the family's.
            if matches!(declaration.role(), Role::Operation | Role::Words) {
                continue;
            }
            let lowered = match declaration.outcome() {
                DeclarationOutcome::Completed { declared_type, .. }
                | DeclarationOutcome::Uncompleted { declared_type } => {
                    Some(Held::Typed(TypeNode::Value(declared_type)))
                },
                DeclarationOutcome::Bodied { body } => {
                    first_type(TermNode::Value(body)).map(Held::Typed)
                },
                DeclarationOutcome::Data(index) => match module.data(index) {
                    Maybe::Present(signature) => {
                        Some(Held::Typed(TypeNode::Value(signature.kind())))
                    },
                    Maybe::Absent(_) => None,
                },
                DeclarationOutcome::Codata(index) => match module.codata(index) {
                    Maybe::Present(signature) => {
                        Some(Held::Typed(TypeNode::Value(signature.kind())))
                    },
                    Maybe::Absent(_) => None,
                },
                DeclarationOutcome::Abstract(sealing) => {
                    Some(Held::Typed(TypeNode::Value(sealing.kind)))
                },
                DeclarationOutcome::World => None,
                DeclarationOutcome::Refused(refusal) => Some(Held::Refused(refusal.to_string())),
            };
            // A declaration the checker refused keeps the type the lowering
            // gave it and gains the checker's refusal; one the lowering gave no
            // type is held by the checker's refusal alone.
            let held = match (lowered, typed.refused().get(&declaration.constant())) {
                (Some(Held::Typed(ty)), Some(&refusal)) => Held::Rejected {
                    ty,
                    refusal: Checked(refusal).to_string(),
                },
                (None, Some(&refusal)) => Held::Refused(Checked(refusal).to_string()),
                (Some(held), _) => held,
                (None, None) => continue,
            };
            for key in [
                declaration.signature(),
                declaration.definition(),
                declaration.duplicate(),
            ] {
                if let Maybe::Present(key) = key
                    && key.source() == own_source
                {
                    let _replaced = declared.insert(key.form(), held.clone());
                }
            }
        }
        let mut orientations = Vec::new();
        for cells in &module.cells().declarations {
            for (&span, direction) in cells.rule_spans.iter().zip(&cells.directions) {
                let Maybe::Present(span) = span
                else {
                    continue;
                };
                let note = match *direction {
                    gandr_surface_lowering::description::written::RuleDirection::LeftToRight => {
                        ChosenDirection::LeftToRight
                    },
                    gandr_surface_lowering::description::written::RuleDirection::RightToLeft => {
                        ChosenDirection::RightToLeft
                    },
                };
                if let Some(span) = own(span, base) {
                    orientations.push((span, note));
                }
            }
        }
        let entries: Vec<Entry> = entries
            .into_iter()
            .filter_map(|entry| {
                Some(Entry {
                    span: own(entry.span, base)?,
                    ..entry
                })
            })
            .collect();
        let mut readings: Vec<(ByteSpan, Reading)> = entries
            .iter()
            .filter(|entry| {
                entry.subject != Subject::Type
                    && matches!(
                        entry.provenance,
                        Provenance::Written | Provenance::Inserted(Insertion::Force)
                    )
            })
            .map(|entry| {
                (entry.span, Reading {
                    binding: if entry.subject == Subject::Binder {
                        Binding::Binds
                    }
                    else {
                        Binding::Uses
                    },
                    polarity: match entry.ty {
                        TypeNode::Value(_) => Polarity::Value,
                        TypeNode::Computation(_) => Polarity::Computation,
                    },
                })
            })
            .collect();
        // A binder is read at the type it binds, whatever term the lowering
        // locates at its name: a function's lambda is located at its
        // parameter. So a span's binder entries come first and decide it.
        readings
            .sort_unstable_by_key(|&(span, reading)| (span, core::cmp::Reverse(reading.binding)));
        readings.dedup_by(|later, kept| {
            let same = later.0 == kept.0;
            if same && later.1.binding == kept.1.binding {
                kept.1.polarity = kept.1.polarity.max(later.1.polarity);
            }
            same
        });
        let referents = Referents::of(
            &module,
            &arena,
            unit,
            base,
            &constructed,
            &hidden,
            &described.uses,
        );
        // A recursive call's head is written with its claim, `plus[<]`: the
        // force runs the whole head, while the use is the name alone, which no
        // entry of its own covers. Such a use reads as the force it begins.
        let headed: Vec<(ByteSpan, Reading)> = entries
            .iter()
            .filter(|entry| {
                entry.subject == Subject::Term
                    && matches!(entry.provenance, Provenance::Inserted(Insertion::Force))
            })
            .filter_map(|entry| {
                let &(used, _) = referents.at(entry.span.start())?;
                (used.start() == entry.span.start()
                    && used != entry.span
                    && readings
                        .binary_search_by_key(&used, |&(span, _)| span)
                        .is_err())
                .then_some((used, Reading {
                    binding: Binding::Uses,
                    polarity: match entry.ty {
                        TypeNode::Value(_) => Polarity::Value,
                        TypeNode::Computation(_) => Polarity::Computation,
                    },
                }))
            })
            .collect();
        readings.extend(headed);
        readings.sort_unstable_by_key(|&(span, _)| span);
        readings.dedup_by(|later, kept| {
            let same = later.0 == kept.0;
            if same {
                kept.1.polarity = kept.1.polarity.max(later.1.polarity);
            }
            same
        });
        let documented = module
            .source_documentations()
            .iter()
            .map(|(&source, written)| (source, written.text().clone()))
            .collect();
        Self {
            entries,
            declared,
            arena,
            names,
            naming: Naming::of(&module, source),
            unit: unit.clone(),
            base,
            families: Families::of(&module),
            contexts,
            orientations,
            signatures,
            opened,
            referents,
            readings,
            in_scope: module.into_in_scope(),
            refused: None,
            documented,
        }
    }

    /// The documentation the unit's source `source` writes of itself.
    ///
    /// # Specification
    /// - requires: nothing — any source is admissible input.
    /// - ensures: the text the lowering filed under `source`, or the
    ///   undocumented absence when it filed none.
    /// - provides: what a hover shows beside an import of the source, and at
    ///   the document's own head.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an imported sibling and an importer each answer their
    ///   own text, and a source writing none the absence.
    /// - witness: `typed::tests::the_table_keeps_each_source_s_own_documentation_1365`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => self.documented.get(&source) == Some(found),
        | Maybe::Absent(_) => !self.documented.contains_key(&source),
    })]
    #[inline]
    pub fn source_documentation(
        &self,
        source: SourceIndex,
    ) -> Maybe<&DocumentationText, documentation::Absent>
    {
        self.documented.get(&source).map_or(
            Maybe::Absent(documentation::Absent::Undocumented),
            Maybe::Present,
        )
    }

    /// Each oriented rule's span and the direction the order chose.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn orientations(&self) -> &[(ByteSpan, ChosenDirection)]
    {
        &self.orientations
    }

    /// The innermost typed node whose span holds `offset`, spelled in `style`
    /// on a page of `page` columns.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: among the entries whose span starts at or before `offset` and
    ///   ends after it, one of the shortest; among those, a binder before a
    ///   term before a type, a written node before an inserted one, and then
    ///   the entry latest in the table. It is spelled at its type and, for a
    ///   term whose last kept type is spelled otherwise, carries that one as
    ///   its expected type. Absent as [`typing::Absent::Untyped`] when no span
    ///   holds `offset`, and as [`typing::Absent::Unspelled`] when the printer
    ///   cannot lay the chosen entry's type out.
    /// - provides: the node a reader pointing at `offset` means.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a variable inside a function body and the body around
    ///   it, a mismatched term, and a position between declarations, separate
    ///   the innermost entry, the enclosing one, the expected type and none.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body scans every entry for the spans holding the offset once; the check scans them once more"
        )
    )]
    #[spec(ensures: |ret| {
        let holding = |entry: &&Entry| entry.span.start() <= offset && offset < entry.span.end();
        let width = |span: ByteSpan| usize::from(span.end()).saturating_sub(usize::from(span.start()));
        match ret {
            Maybe::Present(ref answer) => answer.span.start() <= offset && offset < answer.span.end()
                && self.entries.iter().filter(holding).all(|other| width(other.span) >= width(answer.span)),
            Maybe::Absent(typing::Absent::Untyped) => !self.entries.iter().any(|entry| holding(&entry)),
            Maybe::Absent(typing::Absent::Unspelled) => self.entries.iter().any(|entry| holding(&entry)),
        }
    })]
    #[inline]
    pub fn at(
        &self,
        offset: ByteOffset,
        page: PageWidth,
        style: Style,
    ) -> Maybe<TypedSpan, typing::Absent>
    {
        self.chosen(offset)
            .map_or(Maybe::Absent(typing::Absent::Untyped), |entry| {
                self.answer(entry, page, style)
            })
    }

    /// The span of the entry [`Self::at`] answers `offset` with, unspelled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span of the entry [`Self::at`] chooses at `offset`, or
    ///   `None` when no entry holds it.
    /// - provides: the hover's choice, for a sweep that asks it at every byte
    ///   without spelling a type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus entry gate asks at every byte of every
    ///   source and holds the answer to the innermost node there.
    /// - witness: `tests::entries::every_judged_node_answers_at_its_own_span`
    #[spec(ensures: |ret| ret.is_none_or(|span| span.start() <= offset && offset < span.end()))]
    #[inline]
    #[must_use]
    pub fn answering(
        &self,
        offset: ByteOffset,
    ) -> Option<ByteSpan>
    {
        self.chosen(offset).map(|entry| entry.span)
    }

    /// The written name holding `offset` and what it refers to: the binder or
    /// the declaration the lowering resolved it to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the narrowest use holding `offset` that the table's referent
    ///   index keeps, at its span in the source's own text, with its referent,
    ///   as `Referents::of` states; absent as [`referred::Absent::Unreferred`]
    ///   when no use holds it.
    /// - provides: the answer to a definition request.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's use, a declaration's use, a family in a
    ///   signature, constructors in a term and in a pattern, and a name a
    ///   sibling declares each answer their own site; a binder's own name and a
    ///   keyword answer nothing.
    /// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
    /// - witness: `typed::tests::an_imported_name_refers_to_its_sibling_795`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((span, _)) => span.start() <= offset && offset < span.end(),
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn referent(
        &self,
        offset: ByteOffset,
    ) -> Maybe<(ByteSpan, Referent), referred::Absent>
    {
        self.referents.at(offset).map_or(
            Maybe::Absent(referred::Absent::Unreferred),
            |&(span, target)| Maybe::Present((span, target.referent())),
        )
    }

    /// Every written name lying wholly inside `within` and what it refers to,
    /// ascending by where the name starts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each use the table's referent index keeps whose span, in the
    ///   source's own text, starts at or after `within`'s start and ends at or
    ///   before its end, with its referent, ascending by start; a use crossing
    ///   either end of `within` is not answered.
    /// - provides: the names a copied range of the source uses.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a range holding a declaration's use and a parameter's
    ///   use answers both, a range ending inside a name answers none of it.
    /// - witness: `typed::tests::the_uses_within_a_range_answer_whole`
    #[inline]
    pub fn uses_within(
        &self,
        within: ByteSpan,
    ) -> impl Iterator<Item = (ByteSpan, Referent)> + '_
    {
        self.referents
            .within(within)
            .map(|&(span, target)| (span, target.referent()))
    }

    /// The site of the `half` of the declaration `referent` names, as
    /// written: its own name tile and form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer stands in `referent`'s source; for a declaration
    ///   written in two halves, it is the asked half's name tile and form; for
    ///   one written once, or a referent that names no declaration, `referent`
    ///   itself.
    /// - provides: the answers to a definition request, which asks for the
    ///   definition half, and to a declaration request, which asks for the
    ///   signature half.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name declared in two halves answers each half at
    ///   its own site, and a function written once and a parameter answer
    ///   themselves.
    /// - witness: `typed::tests::each_half_of_a_declaration_answers_its_own_site_1034`
    #[spec(ensures: |ret| ret.source() == referent.source())]
    #[inline]
    #[must_use]
    pub fn half(
        &self,
        referent: Referent,
        half: DeclaredHalf,
    ) -> Referent
    {
        self.referents.half(referent, half)
    }

    /// The span of every written use referring to the name written at `named`
    /// of `source`, in the table's own text, one per start, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the narrowest use starting at each offset whose referent is
    ///   written at `named` of `source`, as `Referents::uses_of` states, in
    ///   order; none for a name no use refers to.
    /// - provides: the uses a highlight, a reference search and a rename
    ///   answer; a name is asked for by where it is written, so another table's
    ///   referent is asked for at this table's index of its source.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the index; the
    ///   index's own lookup states the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's uses, a declaration's uses and a
    ///   constructor's uses in a term and in a pattern are each found, and no
    ///   use of another name is.
    /// - witness: `typed::tests::each_name_is_found_with_every_use_referring_to_it`
    #[inline]
    pub fn uses_of(
        &self,
        source: SourceIndex,
        named: ByteSpan,
    ) -> impl Iterator<Item = ByteSpan> + '_
    {
        self.referents
            .uses_of(source, named)
            .iter()
            .map(|&(_, span)| span)
    }

    /// Each span of the source's own text a written binder or term, or a
    /// force the lowering inserted, covers, ascending, with how the table
    /// reads it: [`Binding::Binds`] when a binder's name is written there,
    /// [`Polarity::Computation`] when a written term or an inserted force
    /// there has a computation type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per span some entry covers whose subject is
    ///   [`Subject::Binder`] or [`Subject::Term`] and whose provenance is
    ///   [`Provenance::Written`] or an inserted [`Insertion::Force`], strictly
    ///   ascending; its binding is [`Binding::Binds`] exactly when such a
    ///   binder entry covers the span, and its polarity is
    ///   [`Polarity::Computation`] exactly when such an entry there has a
    ///   computation type — a binder entry when one covers the span, since a
    ///   binder is read at the type it binds and a function's lambda is located
    ///   at its parameter, and any term entry otherwise, as the force of a
    ///   called name. Any other insertion — an arm's inferred `return`, a
    ///   function's thunk, a match's binding — reads nothing. A use no such
    ///   entry covers that begins an inserted force's wider span, as a
    ///   recursive call's name begins `plus[<]`, reads as that force.
    /// - provides: the modifiers a face marks a written name with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda binder, a `run` binder, a parameter, a
    ///   constructor's own name, a called name, the argument passed to it, a
    ///   binder's use, a value a body answers and a recursive call's name are
    ///   each read apart.
    /// - witness: `typed::tests::a_called_name_runs_and_a_binder_binds`
    /// - witness: `typed::tests::a_recursive_call_s_name_runs_as_its_force_1487`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(*pair, [(first, _), (second, _)] if first < second)))]
    #[inline]
    #[must_use]
    pub fn readings(&self) -> &[(ByteSpan, Reading)]
    {
        &self.readings
    }

    /// The referent whose name, written in the table's own source, holds
    /// `offset` of that source's text: a declaration's, a constructor's, or a
    /// binder some use refers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a referent of the table's own source whose name holds
    ///   `offset`, as `Referents::named_at` states; absent as
    ///   [`referred::Absent::Unreferred`] when no name holds it.
    /// - provides: what a highlight, a reference search or a rename at a
    ///   declaring name means.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration's name, a constructor's name and a used
    ///   parameter's name each answer themselves; a use answers nothing here.
    /// - witness: `typed::tests::each_name_is_found_with_every_use_referring_to_it`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => found.source() == self.own_source()
            && found.named().start() <= offset && offset < found.named().end(),
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn named_at(
        &self,
        offset: ByteOffset,
    ) -> Maybe<Referent, referred::Absent>
    {
        self.referents
            .named_at(self.own_source(), offset)
            .map_or(Maybe::Absent(referred::Absent::Unreferred), Maybe::Present)
    }

    /// The declarations of the data families the type of the node at `offset`
    /// names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a written type, the family the narrowest use holding
    ///   `offset` names, when that use is a written type naming one; for any
    ///   other entry [`Self::at`] chooses at `offset`, the declaration of each
    ///   data family reached from that entry's type through the printer's child
    ///   table, a staged type read at the type its stage refines, once each,
    ///   ascending by constant; empty when no entry holds `offset`.
    /// - provides: the answer to a type-definition request.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the families are read off the type's core graph,
    ///   which only a second walk of that graph could restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursion's staged parameter answers the family its
    ///   stage refines, a function's use every family its type names, and a
    ///   written family answers itself.
    /// - witness: `typed::tests::a_use_s_type_refers_to_the_families_it_names_795`
    #[inline]
    #[must_use]
    pub fn type_referents(
        &self,
        offset: ByteOffset,
    ) -> Vec<Referent>
    {
        let Some(entry) = self.chosen(offset)
        else {
            return Vec::new();
        };
        if entry.subject == Subject::Type {
            return self
                .referents
                .at(offset)
                .and_then(|&(_, target)| target.family())
                .map(|family| Vec::from([family]))
                .unwrap_or_default();
        }
        let names: Vec<Name<'_>> = self
            .names
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let printer = CoreSource::new(&self.arena, &names);
        // The printer writes no stage, so its child table stops at one: a
        // staged type is walked again from the type its stage refines.
        let mut families: Vec<ConstantIndex> = Vec::new();
        let mut walked: BTreeSet<CoreNode> = BTreeSet::new();
        let mut pending = Vec::from([root(entry.ty)]);
        while let Some(from) = pending.pop() {
            if !walked.insert(from) {
                continue;
            }
            for node in Scopes::of(&printer, [from]).reached() {
                let CoreNode::ValueType(ty) = node
                else {
                    continue;
                };
                match self.arena.value_type(ty) {
                    Some(&ValueType::Data { declaration, .. }) => families.push(declaration),
                    Some(&ValueType::Staged { base, .. }) => {
                        pending.push(CoreNode::ValueType(base));
                    },
                    Some(_) | None => {},
                }
            }
        }
        families.sort_unstable();
        families.dedup();
        families
            .into_iter()
            .filter_map(|family| self.referents.declared(family))
            .collect()
    }

    /// The declaration each name `presented` writes stands for, beside where
    /// the name stands in `presented`'s text.
    ///
    /// # Specification
    /// - requires: `presented` was spelled by this table — a [`TypedSpan`]'s
    ///   type or expectation it answered — so its constants are the table's.
    /// - ensures: one pair per name the presentation writes whose constant the
    ///   table declares, in the order written; a bound variable's name is never
    ///   among them, whatever it is spelled.
    /// - provides: what links a printed type's names to their declarations
    ///   without matching its text: a type hint's label parts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function's use spells its type with each family it
    ///   writes linked to the family's declaration, at the bytes of the name,
    ///   and its binders' names unlisted.
    /// - witness: `typed::tests::a_presented_type_links_each_name_it_writes_1441`
    #[spec(ensures: |ret| ret.len() <= presented.names().len()
        && ret.iter().zip(ret.iter().skip(1_usize)).all(|(before, after)| before.0.start() < after.0.start()))]
    #[inline]
    #[must_use]
    pub fn written_referents(
        &self,
        presented: &Presentation,
    ) -> Vec<(WrittenName, Referent)>
    {
        presented
            .names()
            .iter()
            .filter_map(|&name| {
                self.referents
                    .declared(name.constant())
                    .map(|referent| (name, referent))
            })
            .collect()
    }

    /// The source of the table's unit that the table types.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn own_source(&self) -> SourceIndex
    {
        self.unit.source_at(self.base)
    }

    /// The text of the unit's source `source`: from where it starts to where
    /// the next one starts, or to the unit's end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source_text(
        &self,
        source: SourceIndex,
    ) -> Option<SourceText<'_>>
    {
        let sources = self.unit.sources();
        let start = usize::from(sources.get(usize::from(source))?.start());
        let end = sources
            .get(usize::from(source).saturating_add(1_usize))
            .map_or_else(
                || <&str>::from(self.naming.text()).len(),
                |next| usize::from(next.start()),
            );
        <&str>::from(self.naming.text())
            .get(start .. end)
            .map(SourceText::from)
    }

    /// Each name the table's unit declares, a family's constructors included,
    /// with what it names, ascending by where it is written.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per declaration of the unit that is no family's
    ///   operation or words, named by its name tile — [`NameKind::Family`] for
    ///   a described or native family, [`NameKind::Value`] for any other — and
    ///   one [`NameKind::Constructor`] per constructor a family writes, named
    ///   by its name tile and extended by the family's form; a declaration the
    ///   lowering refused included.
    /// - provides: the declared names a completion offers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family, its constructors, a function and a
    ///   sibling's declaration are each named once with their kind.
    /// - witness: `typed::tests::the_declared_names_are_named_with_their_kind_806`
    #[spec(ensures: |ret| ret.is_sorted())]
    #[inline]
    #[must_use]
    pub fn declared_names(&self) -> &[(Referent, NameKind)]
    {
        self.referents.offered()
    }

    /// The span, in the table's own text, of each name its source writes
    /// that nothing declares or binds: where the lowering refused a
    /// declaration as `UnresolvedName` or `UnresolvedTypeHead`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one span per such refusal of a declaration the table's own
    ///   source writes, ascending, as `Referents::of` states; none when the
    ///   lowering resolved every name.
    /// - provides: the names the editor marks as unresolved, an expected
    ///   refusal's included.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unknown term name and an unknown type head are
    ///   each kept at their own spelling, and a declaration that resolves keeps
    ///   nothing; an unknown name beside a form refused as shadowing is kept.
    /// - witness: `typed::tests::a_name_nothing_declares_is_kept_where_it_is_written`
    /// - witness: `typed::tests::a_name_nothing_declares_is_kept_beside_a_form_refused_as_shadowing`
    #[spec(ensures: |ret| ret.is_sorted())]
    #[inline]
    #[must_use]
    pub fn unresolved(&self) -> &[ByteSpan]
    {
        self.referents.unresolved()
    }

    /// The binders in scope at `offset` of the source's own text, innermost
    /// first, a shadowed binder included: each one's written name, and where
    /// the source's own text writes it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for each binder [`InScope::binders_at`] answers at `offset`
    ///   moved into the unit's text, in its order, the text of its name and its
    ///   span moved back into the source's own text; a binder whose name the
    ///   unit's text does not hold, or that lies before the source's own text,
    ///   is skipped.
    /// - provides: the binders a completion at `offset` offers, and the site
    ///   [`Self::at`] types each by.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the chain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern's binder in its arm and not in its sibling,
    ///   a parameter in the body of a refused declaration, each at its written
    ///   name.
    /// - witness: `typed::tests::the_binders_in_scope_are_spelled_in_the_source_s_text_831`
    #[inline]
    pub fn binders_at(
        &self,
        offset: ByteOffset,
    ) -> impl Iterator<Item = (SourceText<'_>, ByteSpan)>
    {
        let base = usize::from(self.base);
        let at = ByteOffset::from(usize::from(offset).saturating_add(base));
        self.in_scope.binders_at(at).filter_map(move |site| {
            let name = <&str>::from(self.naming.text())
                .get(usize::from(site.start()) .. usize::from(site.end()))?;
            let own = ByteSpan::new(
                ByteOffset::from(usize::from(site.start()).checked_sub(base)?),
                ByteOffset::from(usize::from(site.end()).checked_sub(base)?),
            )
            .ok()?;
            Some((SourceText::from(name), own))
        })
    }

    /// The span of every entry, in table order, unspelled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn spans(&self) -> impl Iterator<Item = ByteSpan> + '_
    {
        self.entries.iter().map(|entry| entry.span)
    }

    /// The entry a reader pointing at `offset` means: among the entries
    /// holding it, one of the shortest; then a decode — the type its code
    /// written there denotes, rather than the code — then a binder before a
    /// term before a type, a written node before an inserted one, and the
    /// entry latest in the table.
    ///
    /// # Specification
    /// trivial.
    fn chosen(
        &self,
        offset: ByteOffset,
    ) -> Option<&Entry>
    {
        self.entries
            .iter()
            .enumerate()
            .filter(|&(_, entry)| entry.span.start() <= offset && offset < entry.span.end())
            .min_by_key(|&(position, entry)| {
                (
                    usize::from(entry.span.end()).saturating_sub(usize::from(entry.span.start())),
                    entry.provenance != Provenance::Inserted(Insertion::Decode),
                    entry.subject,
                    matches!(entry.provenance, Provenance::Inserted(_)),
                    core::cmp::Reverse(position),
                )
            })
            .map(|(_, entry)| entry)
    }

    /// Every entry of the table, in the order the typed run finished them,
    /// each spelled in `style` on a page of `page` columns as [`Self::at`]
    /// spells the entry it answers with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one answer per entry, in table order: the entry spelled at
    ///   its type and, for a term whose last kept type is spelled otherwise, at
    ///   that one as its expected type; absent as [`typing::Absent::Unspelled`]
    ///   where the printer cannot lay a type out.
    /// - provides: the whole table, for a sweep that reads every entry.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    /// - executable: none — the answers are a lazy iterator, spelled only as
    ///   the caller draws them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus census reads every entry of every source
    ///   and finds each `?` the printer writes.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    #[inline]
    pub fn entries(
        &self,
        page: PageWidth,
        style: Style,
    ) -> impl Iterator<Item = Maybe<TypedSpan, typing::Absent>> + '_
    {
        self.entries
            .iter()
            .map(move |entry| self.answer(entry, page, style))
    }

    /// Every binder the source wrote whose name overlaps `within`, in table
    /// order, each spelled in `style` on a page of `page` columns as
    /// [`Self::entries`] spells it; the table's other entries are never
    /// spelled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one answer per entry whose subject is [`Subject::Binder`],
    ///   whose provenance is [`Provenance::Written`] and whose span shares a
    ///   byte with `within`, in table order, spelled as [`Self::entries`]
    ///   spells it.
    /// - provides: the binders a face annotates in a window of the source.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    /// - executable: none — the answers are a lazy iterator, spelled only as
    ///   the caller draws them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda's binder and a parameter each answer in a
    ///   window holding them and not in one beside them.
    /// - witness: `typed::tests::the_binders_in_a_window_answer_alone`
    #[inline]
    pub fn binders(
        &self,
        within: ByteSpan,
        page: PageWidth,
        style: Style,
    ) -> impl Iterator<Item = Maybe<TypedSpan, typing::Absent>> + '_
    {
        self.entries
            .iter()
            .filter(move |entry| {
                entry.subject == Subject::Binder
                    && entry.provenance == Provenance::Written
                    && entry.span.start() < within.end()
                    && within.start() < entry.span.end()
            })
            .map(move |entry| self.answer(entry, page, style))
    }

    /// `entry` spelled in `style` on a page of `page` columns.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::at`] spells the entry it chose.
    /// - provides: the one spelling of an entry.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::at`], and nodes checked against the type
    ///   they synthesise, or one spelled alike, answer one type.
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref answer) => answer.span == entry.span && answer.subject == entry.subject,
        Maybe::Absent(typing::Absent::Unspelled) => true,
        Maybe::Absent(typing::Absent::Untyped) => false,
    })]
    fn answer(
        &self,
        entry: &Entry,
        page: PageWidth,
        style: Style,
    ) -> Maybe<TypedSpan, typing::Absent>
    {
        let binders = self.standing(entry.standing);
        let Maybe::Present(ty) = self.spell(entry.ty, &binders, page, style)
        else {
            return Maybe::Absent(typing::Absent::Unspelled);
        };
        let expected = match self.spell(entry.last, &binders, page, style) {
            Maybe::Present(other)
                if entry.last != entry.ty
                    && <Presentation as AsRef<str>>::as_ref(&other) != ty.as_ref() =>
            {
                Maybe::Present(other)
            },
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(checked_against::Absent::Agreed),
        };
        Maybe::Present(TypedSpan {
            span: entry.span,
            subject: entry.subject,
            provenance: entry.provenance,
            ty,
            expected,
        })
    }

    /// The type or refusal of the declaration one of whose forms has the key
    /// `key`, a type spelled in `style` on a page of `page` columns.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lowering's refusal the table holds for the declaration,
    ///   or its type spelled — a declaration the checker refused included;
    ///   absent as [`typing::Absent::Untyped`] when no declaration has the key,
    ///   and as [`typing::Absent::Unspelled`] when the printer cannot lay its
    ///   type out.
    /// - provides: the declaration half of a face's answer.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signature, its definition and a synthesised
    ///   declaration are each keyed at their type.
    /// - witness: `typed::tests::both_halves_of_a_declaration_find_its_type`
    #[spec(ensures: |ret| match (self.declared.get(&key), &ret) {
        (None, &Maybe::Absent(typing::Absent::Untyped))
            | (Some(&(Held::Typed(_) | Held::Rejected { .. })), &(Maybe::Present(Declared::Typed(_)) | Maybe::Absent(typing::Absent::Unspelled))) => true,
        (Some(held), &Maybe::Present(Declared::Refused(ref refusal))) => *held == Held::Refused(refusal.clone()),
        _ => false,
    })]
    #[inline]
    pub fn declared(
        &self,
        key: NodeKey,
        page: PageWidth,
        style: Style,
    ) -> Maybe<Declared, typing::Absent>
    {
        match self.declared.get(&key) {
            Some(&(Held::Typed(node) | Held::Rejected { ty: node, .. })) => {
                match self.spell(node, &Context::default(), page, style) {
                    Maybe::Present(spelled) => Maybe::Present(Declared::Typed(spelled)),
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                }
            },
            Some(&Held::Refused(ref refusal)) => Maybe::Present(Declared::Refused(refusal.clone())),
            None => Maybe::Absent(typing::Absent::Untyped),
        }
    }

    /// The refusal the table holds for the declaration one of whose forms has
    /// the key `key` — the lowering's or the checker's — read without spelling
    /// any type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lowering's refusal [`Self::declared`] answers for `key`,
    ///   or the checker's refusal of a declaration it answers a type for;
    ///   absent as [`unrefused::Absent::Typed`] where it answers a type the
    ///   checker accepted, and as [`unrefused::Absent::Undeclared`] where no
    ///   declaration has the key.
    /// - provides: a face's question whether a declaration was refused, at no
    ///   printer's cost.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused and a typed declaration are each read as
    ///   [`Self::declared`] answers them, and a `data` declaration the checker
    ///   refused answers the checker's refusal as the editor titles it.
    /// - witness: `typed::tests::a_refusal_is_read_as_the_declaration_answers_it`
    /// - witness: `typed::tests::a_checker_refusal_is_held_by_its_declaration_1204`
    #[spec(ensures: |ret| match (self.declared.get(&key), &ret) {
        (Some(&(Held::Refused(ref held) | Held::Rejected { refusal: ref held, .. })), &Maybe::Present(refusal)) => held.as_str() == <&str>::from(refusal),
        (Some(&Held::Typed(_)), &Maybe::Absent(unrefused::Absent::Typed))
            | (None, &Maybe::Absent(unrefused::Absent::Undeclared)) => true,
        _ => false,
    })]
    #[inline]
    pub fn refusal(
        &self,
        key: NodeKey,
    ) -> Maybe<SourceText<'_>, unrefused::Absent>
    {
        match self.declared.get(&key) {
            Some(&(Held::Refused(ref refusal) | Held::Rejected { ref refusal, .. })) => {
                Maybe::Present(SourceText::from(refusal.as_str()))
            },
            Some(&Held::Typed(_)) => Maybe::Absent(unrefused::Absent::Typed),
            None => Maybe::Absent(unrefused::Absent::Undeclared),
        }
    }

    /// The lowering's refusal of the source as a whole, as it reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the refusal's message when the lowering refused the source as
    ///   a whole — its root not a list of declarations, an engine fault
    ///   excepted — and absent as [`wholly::Absent::Lowered`] when it read it.
    /// - provides: a face's account of a source in which the table holds
    ///   nothing, since nothing was lowered.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source refused as a whole keeps the lowering's
    ///   message, and a source of declarations keeps none.
    /// - witness: `typed::tests::a_source_refused_whole_keeps_its_refusal_1201`
    #[spec(ensures: |ret| match (&self.refused, &ret) {
        (&Some(ref held), &Maybe::Present(refusal)) => held.as_str() == <&str>::from(refusal),
        (&None, &Maybe::Absent(wholly::Absent::Lowered)) => true,
        _ => false,
    })]
    #[inline]
    pub fn refused_whole(&self) -> Maybe<SourceText<'_>, wholly::Absent>
    {
        self.refused
            .as_deref()
            .map_or(Maybe::Absent(wholly::Absent::Lowered), |refusal| {
                Maybe::Present(SourceText::from(refusal))
            })
    }

    /// Every declaration's form key with its type or refusal, a type spelled
    /// in `style` on a page of `page` columns, in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one answer per key the table holds, as [`Self::declared`]
    ///   answers that key.
    /// - provides: the declarations, for a sweep that reads every one.
    /// - fails: never; an absence names its reason.
    /// - panics: none.
    /// - executable: none — the answers are a lazy iterator, spelled only as
    ///   the caller draws them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus census reads every declaration of every
    ///   source.
    /// - witness: `typed::tests::both_halves_of_a_declaration_find_its_type`
    #[inline]
    pub fn declarations(
        &self,
        page: PageWidth,
        style: Style,
    ) -> impl Iterator<Item = (NodeKey, Maybe<Declared, typing::Absent>)> + '_
    {
        self.declared
            .keys()
            .map(move |&key| (key, self.declared(key, page, style)))
    }

    /// `node` spelled through the shared printer in `style` on a page of `page`
    /// columns, writing each constant by its name, each variable of `context`
    /// by the name written for its binder, and each capability scope's
    /// region by its scope's name.
    ///
    /// # Specification
    /// trivial.
    fn spell(
        &self,
        node: TypeNode,
        context: &Context,
        page: PageWidth,
        style: Style,
    ) -> Maybe<Presentation, typing::Absent>
    {
        self.spell_in(&self.arena, node, context, &Read::default(), page, style)
    }

    /// `node` of `arena` spelled as [`Self::spell`] spells a node of the
    /// table's own arena: `arena` holds the table's nodes at their ids, so the
    /// constants and constructors are named alike, each dependent arrow
    /// `read` names past them binds the name it holds, and each type `read`
    /// relates spells as the relation it was written as.
    ///
    /// # Specification
    /// trivial.
    fn spell_in(
        &self,
        arena: &CoreArena,
        node: TypeNode,
        context: &Context,
        read: &Read,
        page: PageWidth,
        style: Style,
    ) -> Maybe<Presentation, typing::Absent>
    {
        let names: Vec<Name<'_>> = self
            .names
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let binders: Vec<Option<Name<'_>>> = context
            .binders
            .iter()
            .map(|name| name.as_deref().map(Name::from))
            .collect();
        let regions: Vec<Option<Name<'_>>> = context
            .regions
            .iter()
            .map(|name| name.as_deref().map(Name::from))
            .collect();
        let mut arrows: Vec<(CompTypeId, Name<'_>)> = self
            .naming
            .arrows()
            .iter()
            .filter_map(|&(arrow, span)| {
                <&str>::from(self.naming.text())
                    .get(usize::from(span.start()) .. usize::from(span.end()))
                    .map(|name| (arrow, Name::from(name)))
            })
            .chain(
                read.arrows
                    .iter()
                    .map(|&(arrow, ref name)| (arrow, Name::from(name.as_str()))),
            )
            .collect();
        arrows.sort_by_key(|&(arrow, _)| arrow);
        let pairs = labelled(self.naming.pairs(), self.naming.text(), &read.pairs);
        let seconds = labelled(self.naming.seconds(), self.naming.text(), &read.seconds);
        let mut relations: Vec<(ValueTypeId, Relation)> = self
            .naming
            .relations()
            .iter()
            .chain(&read.relations)
            .copied()
            .collect();
        relations.sort_by_key(|&(related, _)| related);
        let constructors = self.families.naming(&names);
        let printer = CoreSource::new(arena, &names)
            .naming(&constructors)
            .naming_arrows(&arrows)
            .naming_pairs(&pairs, &seconds)
            .relating(&relations)
            .within(&binders)
            .scoped(&regions);
        present_type(&printer, root(node), page, style)
            .map_or(Maybe::Absent(typing::Absent::Unspelled), Maybe::Present)
    }

    /// The context an entry standing at `standing` is read under: the names
    /// of its intuitionistic binders and of the regions around it, each
    /// outermost first — for a judged node, by walking the scopes of its
    /// declaration alone; for a described member, its context's names and no
    /// region.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a judged node, for each intuitionistic binder from the
    ///   outermost to the innermost around the node's place under as many of
    ///   them as its type was judged under — its first place where the table
    ///   keeps no such depth or no place is under it — the name
    ///   [`Naming::scoped`] gives it, and among the regions the name of each
    ///   capability scope and each hold around that place, as
    ///   [`gandr_surface_diagnostics::Scoped::regions_at`] gives them; for a
    ///   part standing under the parts before it, those of its match's node,
    ///   then each earlier part's name, of no known type; for a described
    ///   member, each name its context binds; empty for a closed node or one
    ///   its declaration does not reach.
    /// - provides: the context an entry's type is spelled in.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Naming::scoped`], whose witness spells through
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Naming::scoped`]: a body's terms answer under
    ///   their binders' names, and an endpoint under its signature's; a
    ///   theory's operation under the sorts before it; a capability inside a
    ///   scope's subject names the scope, and a type kept at a hold names the
    ///   hold, past the scopes and holds around it; a node the term shares
    ///   between places of other depths answers at the place it was judged.
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_scoped_capability_answers_at_its_scope`
    /// - witness: `typed::tests::a_kept_type_answers_at_the_hold_it_is_kept_in`
    /// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
    /// - witness: `typed::tests::a_dependent_record_spells_its_variables_where_it_stands_1515`
    fn standing(
        &self,
        standing: Standing,
    ) -> Context
    {
        let (
            Within {
                constant,
                node,
                depth,
            },
            parted,
        ) = match standing {
            Standing::Closed => return Context::default(),
            Standing::Named(context) => {
                return Context {
                    binders: self
                        .contexts
                        .get(context.0)
                        .map(|names| names.iter().cloned().map(Some).collect())
                        .unwrap_or_default(),
                    regions: Vec::new(),
                    types: Vec::new(),
                };
            },
            Standing::Judged(within) => (within, None),
            Standing::Parted(within, earlier) => (within, Some(earlier)),
        };
        let Some(roots) = self.naming.roots(constant)
        else {
            return Context::default();
        };
        let scoped = self.naming.scoped(&self.arena, &self.names, roots);
        // A node the term shares between places of other depths is read at
        // the place its type was judged at.
        let (around, regions) = depth.map_or_else(
            || (scoped.around(node), scoped.regions(node)),
            |depth| {
                (
                    scoped.around_at(node, depth),
                    scoped.regions_at(node, depth),
                )
            },
        );
        let mut context = Context::default();
        for binder in around.unwrap_or_default() {
            context.binders.push(binder.name.map(String::from));
            context.types.push(self.bound_type(binder.opener));
        }
        context.regions = regions
            .unwrap_or_default()
            .into_iter()
            .map(|region| region.name.map(String::from))
            .collect();
        for name in parted
            .and_then(|earlier| self.contexts.get(earlier.0))
            .into_iter()
            .flatten()
        {
            context.binders.push(Some(name.clone()));
            context.types.push(None);
        }
        context
    }

    /// The type the binder `opener` opens binds, in the context of the
    /// binders around it, where the table knows it: a dependent arrow's
    /// domain, a static Π's, a dependent pair's first component's, and a term
    /// former's as [`Self::opened`] keeps it.
    ///
    /// # Specification
    /// trivial.
    fn bound_type(
        &self,
        opener: CoreNode,
    ) -> Option<ValueTypeId>
    {
        match opener {
            CoreNode::CompType(id) => match self.arena.comp_type(id) {
                Some(&CompType::Pi { domain, .. }) => Some(domain),
                Some(_) | None => None,
            },
            CoreNode::ValueType(id) => match self.arena.value_type(id) {
                Some(
                    &(ValueType::StaticPi { domain: bound, .. }
                    | ValueType::Sigma { first: bound, .. }),
                ) => Some(bound),
                Some(_) | None => None,
            },
            CoreNode::Computation(_) | CoreNode::Value(_) => self
                .opened
                .binary_search_by_key(&opener, |&(held, _)| held)
                .ok()
                .and_then(|at| self.opened.get(at))
                .map(|&(_, ty)| ty),
        }
    }

    /// The binders of `context` declared as parameters, each type spelled
    /// under the parameters before it, a binder the source names nothing
    /// named afresh.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one parameter per binder of `context`, outermost first, each
    ///   `name : type, ` with its type spelled in `style` on a page of `page`
    ///   columns under the names before it; none when `context` binds nothing,
    ///   or a binder's type is unknown to the table or spells a `?`.
    /// - provides: the context [`Self::read_back`] reads an open type under.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::read_back`], whose witnesses read open
    ///   types through it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read_back`].
    /// - witness: `typed::tests::a_printed_type_reads_back_to_its_certificate`
    fn telescope(
        &self,
        context: &Context,
        page: PageWidth,
        style: Style,
    ) -> Option<Under>
    {
        if context.binders.is_empty() {
            return None;
        }
        let mut parameters = String::new();
        let mut names: Vec<Option<String>> = Vec::with_capacity(context.binders.len());
        for (at, name) in context.binders.iter().enumerate() {
            let ty = context.types.get(at).copied().flatten()?;
            let before = Context {
                binders: names.clone(),
                regions: Vec::new(),
                types: Vec::new(),
            };
            let Maybe::Present(spelled) = self.spell(TypeNode::Value(ty), &before, page, style)
            else {
                return None;
            };
            if !spelled.unspelled().is_empty() {
                return None;
            }
            let name = name
                .clone()
                .unwrap_or_else(|| format!("read_back_bound_{at}"));
            for part in [name.as_str(), " : "] {
                parameters.push_str(part);
            }
            // Formatting into a `String` cannot fail.
            let _written =
                core::fmt::Write::write_fmt(&mut parameters, format_args!("{spelled}, "));
            names.push(Some(name));
        }
        Some(Under {
            parameters,
            context: Context {
                binders: names,
                regions: context.regions.clone(),
                types: context.types.clone(),
            },
        })
    }

    /// Every type the table prints — each entry's own, the type an outer
    /// judgement checked a term against, each declaration's — spelled in
    /// `style` on a page of `page` columns and read back: parsed as a
    /// signature's type, or as a parameter's under parameters declaring the
    /// binders it names, lowered after the source the table was built from,
    /// and compared with the type node the table holds.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the table was built under.
    /// - ensures: one read back per printed type, entries in table order then
    ///   declarations in key order, each with the type as [`Self::at`] or
    ///   [`Self::declared`] prints it. A type the printer cannot lay out is
    ///   [`RoundTrip::Unspelled`]; one holding a `?` the printer wrote is
    ///   [`RoundTrip::Unknown`]. One whose spelling under the node's binders
    ///   differs from its spelling under none names a binder: when the table
    ///   knows every binder's type and spells it, the binders are declared as
    ///   the parameters of a fresh function, `def f(x₁ : A₁, …, xₙ : Aₙ, it :
    ///   T) -> -F Unit`, each `Aᵢ` spelled under the names before it, and the
    ///   type read as `it`'s under all `n`, the binders the lowering dropped
    ///   from a non-dependent arrow put back; it is [`RoundTrip::Open`] when
    ///   the table does not know a binder's type — a capability scope's, a
    ///   described member's — or the function does not lower. A closed one that
    ///   does not parse as the type of `def x : … ;` with no repair is
    ///   [`RoundTrip::Unparsed`]. Every other is appended to the source as a
    ///   signature of a fresh name — a computation type `C` as `+U (C)` — the
    ///   whole lowered once in the unit the table was built in, and is
    ///   [`RoundTrip::Equal`] when the type read is the table's node, `U C` for
    ///   a computation type, compared by [`equal_type_reading`] under the
    ///   source's data signatures — the same syntax with path evidence erased,
    ///   a type of words as the path at its point, a session type by its
    ///   protocol's behaviour from its state; [`RoundTrip::Different`]
    ///   otherwise; and [`RoundTrip::Refused`] with the refusal when the
    ///   lowering refused a closed signature or the whole source. Each type
    ///   read is printed again under the same binders, with the names, labels
    ///   and relations the reread recorded for it, standing also at every copy
    ///   the put-back binders made of it.
    /// - provides: the read-back half of the hover's content guarantee.
    /// - fails: never; a type that does not read back says why.
    /// - panics: none.
    /// - intension: one lowering per call, whatever the number of types; equal
    ///   declarations are appended once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data type, a thunked function type in its sugared
    ///   spelling, a universe, a computation type and a declaration read back
    ///   equal; a term typed under parameters and a bind, one of them a binder
    ///   the type does not name, reads back equal under them; a term whose two
    ///   types disagree reads back at both; a type of a source that imports a
    ///   sibling reads back beside it; and the corpus census reads back every
    ///   printed type of every source, failing on a class the findings do not
    ///   pin.
    /// - witness: `typed::tests::a_printed_type_reads_back_to_its_certificate`
    /// - witness: `typed::tests::a_record_parameter_reprints_with_its_labels_1655`
    /// - witness: `typed::tests::an_importer_s_value_reads_back_beside_its_sibling_552`
    /// - witness: `typed::tests::a_mismatched_term_reads_back_at_both_its_types`
    /// - witness: `typed::tests::a_term_checked_against_a_type_spelled_alike_reads_back_once_1791`
    /// - witness: `tests::census::sweeps::every_printed_type_reads_back_to_its_certificate`
    #[spec(ensures: |ret| ret.len() >= self.entries.len())]
    #[inline]
    #[must_use]
    pub fn read_back(
        &self,
        grammar: &Pbg,
        page: PageWidth,
        style: Style,
    ) -> Vec<ReadBack>
    {
        // Each printed type with the node it was printed from, its trip when
        // it is settled before any lowering, and for a type naming a binder
        // the binders it stands under with the parameters declaring them.
        let mut printed: Vec<Printed> = Vec::new();
        for entry in &self.entries {
            let binders = self.standing(entry.standing);
            let own = self.spell(entry.ty, &binders, page, style);
            let mut sides = Vec::from([(ReadSite::Own(entry.span), entry.ty, own.clone())]);
            if entry.last != entry.ty {
                let last = self.spell(entry.last, &binders, page, style);
                if !matches!((&last, &own), (Maybe::Present(last), Maybe::Present(own))
                    if <Presentation as AsRef<str>>::as_ref(last) == own.as_ref())
                {
                    sides.push((ReadSite::CheckedAgainst(entry.span), entry.last, last));
                }
            }
            for (site, node, spelled) in sides {
                printed.push(match spelled {
                    Maybe::Present(spelled) => {
                        let closed = self.spell(node, &Context::default(), page, style);
                        let (settled, under) = if !spelled.unspelled().is_empty() {
                            (Some(RoundTrip::Unknown), None)
                        }
                        else if matches!(closed, Maybe::Present(ref closed) if *closed == spelled)
                        {
                            (None, None)
                        }
                        else {
                            self.telescope(&binders, page, style)
                                .map_or((Some(RoundTrip::Open), None), |under| (None, Some(under)))
                        };
                        Printed {
                            site,
                            node,
                            spelled: spelled.to_string(),
                            settled,
                            under,
                        }
                    },
                    Maybe::Absent(_) => Printed {
                        site,
                        node,
                        spelled: String::new(),
                        settled: Some(RoundTrip::Unspelled),
                        under: None,
                    },
                });
            }
        }
        for (&key, held) in &self.declared {
            if let Held::Typed(node) | Held::Rejected { ty: node, .. } = *held {
                let site = ReadSite::Declared(key);
                printed.push(match self.spell(node, &Context::default(), page, style) {
                    Maybe::Present(spelled) => Printed {
                        site,
                        node,
                        settled: (!spelled.unspelled().is_empty()).then_some(RoundTrip::Unknown),
                        spelled: spelled.to_string(),
                        under: None,
                    },
                    Maybe::Absent(_) => Printed {
                        site,
                        node,
                        spelled: String::new(),
                        settled: Some(RoundTrip::Unspelled),
                        under: None,
                    },
                });
            }
        }
        // Each distinct declaration that parses whole, appended once under a
        // fresh name: a closed type as a signature, a type naming binders as
        // the last parameter of a function whose parameters declare them.
        let signature = |node: TypeNode, spelled: &str| match node {
            TypeNode::Value(_) => String::from(spelled),
            TypeNode::Computation(_) => format!("+U ({spelled})"),
        };
        let probe = |node: TypeNode, spelled: &str, under: Option<&Under>| {
            under.map_or_else(
                || format!(" : {} ;\n", signature(node, spelled)),
                |under| {
                    format!(
                        "({}read_back_it : {}) -> -F Unit {{ return unit }}\n",
                        under.parameters,
                        signature(node, spelled),
                    )
                },
            )
        };
        let mut appended: BTreeMap<String, String> = BTreeMap::new();
        // Each function's name with how many binders its parameters declare
        // before the read type's.
        let mut parameterised: BTreeMap<String, usize> = BTreeMap::new();
        let mut augmented = String::from(<&str>::from(self.naming.text()));
        let mut whole = String::new();
        for &Printed {
            node,
            ref spelled,
            ref settled,
            ref under,
            ..
        } in &printed
        {
            if settled.is_some() {
                continue;
            }
            let written = probe(node, spelled, under.as_ref());
            if appended.contains_key(&written) {
                continue;
            }
            whole.clear();
            for part in ["def read_back", written.as_str()] {
                whole.push_str(part);
            }
            if parse(grammar, SourceText::from(whole.as_str()))
                .is_ok_and(|parsed| parsed.obligations().is_empty())
            {
                let name = format!("read_back_{}", appended.len());
                for part in ["\ndef ", name.as_str(), written.as_str()] {
                    augmented.push_str(part);
                }
                if let Some(under) = under.as_ref() {
                    let _fresh = parameterised.insert(name.clone(), under.context.binders.len());
                }
                let _fresh = appended.insert(written, name);
            }
        }
        // The appended types, imported into a copy of the table's arena beside
        // the nodes they are compared with.
        let mut arena = self.arena.clone();
        let held: Vec<ValueTypeId> = printed
            .iter()
            .map(|&Printed { node, .. }| match node {
                TypeNode::Value(id) => id,
                TypeNode::Computation(id) => arena.value_type_thunk(id),
            })
            .collect();
        let mut lowered: BTreeMap<String, Result<ValueTypeId, String>> = BTreeMap::new();
        // The names the lowering keeps beside the read types' dependent
        // arrows, and the relations it records for the types written as one,
        // at their images, so a reprint binds and spells what was written.
        let mut read_back = Read::default();
        match lower_unit_source(
            grammar,
            SourceText::from(augmented.as_str()),
            &self.unit,
            &mut LoweringCount::default(),
        )
        .map(Lowering::into_lowered)
        {
            Ok(Lowered::Module {
                module,
                arena: read,
            }) => {
                let mut importer = TypeImporter::new(&read, &mut arena);
                for declaration in module.declarations() {
                    let name = declaration.name();
                    if !name.as_ref().starts_with("read_back_") {
                        continue;
                    }
                    let outcome = match declaration.outcome() {
                        DeclarationOutcome::Uncompleted { declared_type }
                        | DeclarationOutcome::Completed { declared_type, .. } => importer
                            .value_type(declared_type)
                            .map_err(|fault| format!("{fault:?}")),
                        DeclarationOutcome::Refused(refusal) => Err(refusal.to_string()),
                        other @ (DeclarationOutcome::Bodied { .. }
                        | DeclarationOutcome::Data(_)
                        | DeclarationOutcome::Codata(_)
                        | DeclarationOutcome::Abstract(_)
                        | DeclarationOutcome::World) => Err(format!("{other:?}")),
                    };
                    let _first = lowered.insert(String::from(name.as_ref()), outcome);
                }
                for &(arrow, origin) in module.origins().arrows() {
                    let span = origin.span();
                    if let (Some(image), Some(name)) = (
                        importer.comp_type_image(arrow),
                        augmented.get(usize::from(span.start()) .. usize::from(span.end())),
                    ) {
                        read_back.arrows.push((image, String::from(name)));
                    }
                }
                for (named, kept) in [
                    (module.origins().pairs(), &mut read_back.pairs),
                    (module.origins().seconds(), &mut read_back.seconds),
                ] {
                    for &(pair, origin) in named {
                        let span = origin.span();
                        if let (Some(image), Some(name)) = (
                            importer.value_type_image(pair),
                            augmented.get(usize::from(span.start()) .. usize::from(span.end())),
                        ) {
                            kept.push((image, String::from(name)));
                        }
                    }
                }
                for &(related, relation) in module.origins().relations() {
                    if let Some(image) = importer.value_type_image(related) {
                        read_back.relations.push((image, relation));
                    }
                }
            },
            Ok(Lowered::Refused(refusal)) => {
                for name in appended.values() {
                    let _first = lowered.insert(name.clone(), Err(refusal.to_string()));
                }
            },
            Err(fault) => {
                for name in appended.values() {
                    let _first = lowered.insert(name.clone(), Err(fault.to_string()));
                }
            },
        }
        let last_parameter = |arena: &mut CoreArena,
                              declared: ValueTypeId,
                              count: usize,
                              carried: &mut Vec<Carried>|
         -> Option<ValueTypeId> {
            let &ValueType::Thunk(mut at) = arena.value_type(declared)?
            else {
                return None;
            };
            // Whether each parameter before the last kept its binder.
            let mut kept: Vec<bool> = Vec::with_capacity(count);
            loop {
                let (domain, codomain, dependent) = match arena.comp_type(at) {
                    Some(&CompType::Pi { domain, codomain }) => (domain, codomain, true),
                    Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, false),
                    Some(_) | None => return None,
                };
                if kept.len() == count {
                    let mut ty = domain;
                    for dropped in (0 .. count).rev() {
                        if kept.get(dropped) != Some(&false) {
                            continue;
                        }
                        let scope = kept
                            .iter()
                            .skip(dropped)
                            .skip(1)
                            .filter(|&&present| present)
                            .fold(Binders::NONE, |scope, _| scope.deeper());
                        ty = shift_value_type_under(arena, ty, scope, Binders::ONE)
                            .settle_traced(arena, carried);
                        if let Some(slot) = kept.get_mut(dropped) {
                            *slot = true;
                        }
                    }
                    return Some(ty);
                }
                kept.push(dependent);
                at = codomain;
            }
        };
        // A function's read type is its last parameter's, read under every
        // parameter before it: the lowering forms a parameter its codomain
        // never names as a non-dependent arrow, its binder dropped, so each
        // dropped binder is put back around the type, innermost first.
        let mut carried: Vec<Carried> = Vec::new();
        for (name, &count) in &parameterised {
            let Some(read) = lowered.get_mut(name)
            else {
                continue;
            };
            let Ok(declared) = *read
            else {
                continue;
            };
            *read = last_parameter(&mut arena, declared, count, &mut carried)
                .ok_or_else(|| String::from("the declaration is no function of its parameters"));
        }
        // A type the lowering recorded as written as a relation, a pair it
        // recorded labels for, or a dependent arrow it recorded its binder's
        // name for, stands at each copy a shift made of it, so a type read
        // under a dropped binder reprints as written (#674, #1655, #1751). The
        // copies are taken in the order the shifts made them, so a copy of a
        // copy finds its source's; a type recorded twice keeps its first.
        let mut related: BTreeMap<ValueTypeId, Relation> = BTreeMap::new();
        for &(ty, relation) in &read_back.relations {
            related.entry(ty).or_insert(relation);
        }
        let mut named: BTreeMap<CompTypeId, String> = BTreeMap::new();
        for &(arrow, ref name) in &read_back.arrows {
            named.entry(arrow).or_insert_with(|| name.clone());
        }
        // Each pair's first recorded label, by its place among the kept ones;
        // a copy stands at its source's place, so a copy of a copy reaches
        // the label recorded for the first.
        let first = |kept: &[(ValueTypeId, String)]| -> BTreeMap<ValueTypeId, usize> {
            let mut first = BTreeMap::new();
            for (at, &(pair, _)) in kept.iter().enumerate() {
                first.entry(pair).or_insert(at);
            }
            first
        };
        let mut binders = first(&read_back.pairs);
        let mut seconds = first(&read_back.seconds);
        let mut copied_binders: Vec<(ValueTypeId, usize)> = Vec::new();
        let mut copied_seconds: Vec<(ValueTypeId, usize)> = Vec::new();
        for copy in carried {
            let (source, image) = match copy {
                Carried::ValueType(source, image) => (source, image),
                Carried::CompType(source, image) => {
                    if let Some(name) = named.get(&source).cloned() {
                        read_back.arrows.push((image, name.clone()));
                        named.entry(image).or_insert(name);
                    }
                    continue;
                },
                Carried::Value(..) | Carried::Computation(..) => continue,
            };
            if let Some(&relation) = related.get(&source) {
                read_back.relations.push((image, relation));
                related.entry(image).or_insert(relation);
            }
            for (labels, copied) in [
                (&mut binders, &mut copied_binders),
                (&mut seconds, &mut copied_seconds),
            ] {
                if let Some(&at) = labels.get(&source) {
                    let _first = labels.entry(image).or_insert(at);
                    copied.push((image, at));
                }
            }
        }
        for (copied, kept) in [
            (copied_binders, &mut read_back.pairs),
            (copied_seconds, &mut read_back.seconds),
        ] {
            let labelled: Vec<(ValueTypeId, String)> = copied
                .into_iter()
                .filter_map(|(image, at)| {
                    kept.get(at).map(|&(_, ref label)| (image, label.clone()))
                })
                .collect();
            kept.extend(labelled);
        }
        printed
            .into_iter()
            .zip(held)
            .map(
                |(
                    Printed {
                        site,
                        node,
                        spelled,
                        settled,
                        under,
                    },
                    held,
                )| {
                    let read = match settled {
                        Some(_) => None,
                        None => appended
                            .get(&probe(node, &spelled, under.as_ref()))
                            .and_then(|name| lowered.get(name)),
                    };
                    // A type naming binders that the declaration of its binders
                    // does not read stays open: the declaration is the table's
                    // own rendering of the context, not the source's.
                    let trip = settled.unwrap_or_else(|| match (read, &under) {
                        (None | Some(&Err(_)), &Some(_)) => RoundTrip::Open,
                        (None, &None) => RoundTrip::Unparsed,
                        (Some(&Err(ref refusal)), &None) => RoundTrip::Refused(refusal.clone()),
                        (Some(&Ok(read)), _) => {
                            match equal_type_reading(&arena, &self.signatures, held, read) {
                                CertificateEquality::Equal => RoundTrip::Equal,
                                CertificateEquality::Different => RoundTrip::Different,
                            }
                        },
                    });
                    // The lowered type printed again under the same binders, a
                    // computation type from under the thunk its signature wraps
                    // it in.
                    let reprinted = match read {
                        Some(&Ok(read)) => {
                            let again = match (node, arena.value_type(read)) {
                                (TypeNode::Computation(_), Some(&ValueType::Thunk(inner))) => {
                                    TypeNode::Computation(inner)
                                },
                                (TypeNode::Computation(_) | TypeNode::Value(_), _) => {
                                    TypeNode::Value(read)
                                },
                            };
                            let context = under.map(|under| under.context).unwrap_or_default();
                            match self.spell_in(&arena, again, &context, &read_back, page, style) {
                                Maybe::Present(again) => Maybe::Present(again.to_string()),
                                Maybe::Absent(_) => Maybe::Absent(reprinted::Absent::Unspelled),
                            }
                        },
                        Some(&Err(_)) | None => Maybe::Absent(reprinted::Absent::Unlowered),
                    };
                    ReadBack {
                        site,
                        spelled,
                        trip,
                        reprinted,
                    }
                },
            )
            .collect()
    }

    /// The value `written` spells, read in the source the table was built
    /// from as the value a run of the declaration named `signed` returns and
    /// printed again as a run prints it: the printer's fixed point over the
    /// values it prints, `print(parse(print(v)))`.
    ///
    /// The declaration is named, not numbered (#610): a run's constants are
    /// the program of the component judged, which can hold sources the
    /// table's unit does not, so its numbering is not the table's.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the table was built under.
    /// - ensures: `written` appended to the source as the body of a fresh thunk
    ///   declaration, read first as it is written, with no signature: the whole
    ///   lowered once in the unit the table was built in, an importer beside
    ///   the siblings it reads, and the thunk's computation printed as a run's
    ///   value prints, on one line in the sugared form, its constants and
    ///   constructors named as the table names them. Where that reading is
    ///   refused — a constructor needs the type its position states — and the
    ///   declaration named `signed` declares a type, the declaration is signed
    ///   with it, with the computation returning it when it is no thunk, the
    ///   whole source judged and the fresh declaration run, its value spelled
    ///   as the run spells it; [`reprinted::Absent::Unrun`] when the source did
    ///   not settle or the run reached no value.
    ///   [`reprinted::Absent::Unlowered`] when the lowering refused it or the
    ///   source, and [`reprinted::Absent::Unspelled`] when the printer could
    ///   not lay it out.
    /// - provides: the reprint a presentation census compares a printed value
    ///   with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the census reprints every run value and normal form
    ///   the corpus states; a value whose spelling lowers to another prints
    ///   otherwise and fails it. A value of a source that imports a sibling
    ///   reprints both ways: as written, and run under its signature, found by
    ///   its name in a component with more members than its imports.
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    /// - witness: `typed::tests::an_importer_s_value_reads_back_beside_its_sibling_552`
    /// - witness: `typed::tests::a_member_s_value_reprints_under_its_own_declaration_610`
    #[inline]
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    pub fn reprint_value(
        &self,
        grammar: &Pbg,
        signed: Maybe<Name<'_>, signed::Absent>,
        written: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        const NAME: &str = REPRINTED;
        let declared = match signed {
            Maybe::Present(signed) => self
                .names
                .iter()
                .position(|name| name.as_str() == signed.as_ref())
                .map(ConstantIndex::from)
                .and_then(|signed| self.naming.roots(signed))
                .and_then(|[declared, body]| body.and(declared)),
            Maybe::Absent(signed::Absent::Unsigned) => None,
        };
        let signature = if let Some(CoreNode::ValueType(declared)) = declared {
            let Maybe::Present(spelled) = self.spell(
                TypeNode::Value(declared),
                &Context::default(),
                PageWidth::from(u32::from(u16::MAX)),
                Form::Sugared.into(),
            )
            else {
                return Maybe::Absent(reprinted::Absent::Unspelled);
            };
            if matches!(self.arena.value_type(declared), Some(&ValueType::Thunk(_))) {
                format!("\ndef {NAME} : {spelled} ;")
            }
            else {
                format!("\ndef {NAME} : +U (-F ({spelled})) ;")
            }
        }
        else {
            String::new()
        };
        let body = format!("\ndef {NAME} = thunk {{ {written} }} ;\n");
        let mut unsigned = String::from(<&str>::from(self.naming.text()));
        unsigned.push_str(&body);
        match self.lowered_reprint(grammar, SourceText::from(unsigned.as_str())) {
            Maybe::Absent(reprinted::Absent::Unlowered) if !signature.is_empty() => {
                let mut signed = String::from(<&str>::from(self.naming.text()));
                signed.push_str(&signature);
                signed.push_str(&body);
                self.run_reprinted(grammar, SourceText::from(signed.as_str()))
            },
            again @ (Maybe::Present(_) | Maybe::Absent(_)) => again,
        }
    }

    /// The normal form `written` states for the block named `block`, read
    /// back and spelled again: the fixed point of a `normalizes` row's right
    /// side.
    ///
    /// A family's normal form is its constructors, a value the top level
    /// names, so it reprints as [`Self::reprint_value`] reprints a value. A
    /// `theory`'s is a term of its block, whose operations no top-level
    /// declaration names (#669), so it is read as a call under the block's
    /// rules and spelled again as the engine spells a normal form,
    /// `spell(nf(read(spell(t))))`.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the table was built under.
    /// - ensures: for a `data` family named `block`, or an operation one
    ///   declares, [`Self::reprint_value`] of `written`, unsigned; for any
    ///   other declaration named `block`, the spelling of
    ///   [`LoweredModule::normal_form`]'s answer for `written` against it, in
    ///   the table's own source lowered once in the unit the table was built
    ///   in; [`reprinted::Absent::Unlowered`] when the lowering refuses the
    ///   source, no declaration is named `block`, or the block reads no normal
    ///   form for `written`.
    /// - provides: the reprint a census compares a stated normal form with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a theory's normal form reads back as written, a call
    ///   reads to its normal form, and a name that is no block reads nothing;
    ///   the census reads the corpus's family rows as values.
    /// - witness: `typed::tests::a_theory_s_normal_form_reads_back_under_its_rules_669`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    #[inline]
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    pub fn reprint_normal_form(
        &self,
        grammar: &Pbg,
        block: Name<'_>,
        written: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        let Ok(Lowered::Module { module, .. }) = lower_unit_source(
            grammar,
            self.naming.text(),
            &self.unit,
            &mut LoweringCount::default(),
        )
        .map(Lowering::into_lowered)
        else {
            return Maybe::Absent(reprinted::Absent::Unlowered);
        };
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == block.as_ref())
        else {
            return Maybe::Absent(reprinted::Absent::Unlowered);
        };
        if matches!(declaration.outcome(), DeclarationOutcome::Data(_))
            || declaration.role() == Role::Operation
        {
            return self.reprint_value(grammar, Maybe::Absent(signed::Absent::Unsigned), written);
        }
        module
            .normal_form(declaration, CallText::from(<&str>::from(written)))
            .ok()
            .map(|normal| normal.spelling())
            .filter(|again| !again.is_empty())
            .map_or(Maybe::Absent(reprinted::Absent::Unlowered), Maybe::Present)
    }

    /// The thunk the declaration [`REPRINTED`] of `source` defines, lowered
    /// and its computation printed as a run's value prints.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the source is read under; `source`
    ///   is the text the table's unit lays out, the declaration appended.
    /// - ensures: the computation on one line in the sugared form, its
    ///   constants and constructors named as the table names them;
    ///   [`reprinted::Absent::Unlowered`] when the lowering in the table's unit
    ///   refused the source or the declaration, or defined no thunk, and
    ///   [`reprinted::Absent::Unspelled`] when the printer could not lay it
    ///   out.
    /// - provides: the unsigned half of [`Self::reprint_value`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reprint_value`].
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    /// - witness: `typed::tests::an_importer_s_value_reads_back_beside_its_sibling_552`
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    fn lowered_reprint(
        &self,
        grammar: &Pbg,
        source: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        let Ok(Lowered::Module { module, arena }) =
            lower_unit_source(grammar, source, &self.unit, &mut LoweringCount::default())
                .map(Lowering::into_lowered)
        else {
            return Maybe::Absent(reprinted::Absent::Unlowered);
        };
        let thunk = module.declarations().iter().find_map(|declaration| {
            if declaration.name().as_ref() != REPRINTED {
                return None;
            }
            match declaration.outcome() {
                DeclarationOutcome::Bodied { body }
                | DeclarationOutcome::Completed { body, .. } => Some(body),
                DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => None,
            }
        });
        let Some(&Value::Thunk(computation)) = thunk.and_then(|body| arena.value(body))
        else {
            return Maybe::Absent(reprinted::Absent::Unlowered);
        };
        let names: Vec<Name<'_>> = self
            .names
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        // The cases are this lowering's own: the table's are another arena's.
        let families = Families::of(&module);
        let constructors = families.naming(&names);
        let printer = CoreSource::new(&arena, &names).naming(&constructors);
        present_computation_line(
            &printer,
            CoreNode::Computation(computation),
            Form::Sugared.into(),
        )
        .map_or(Maybe::Absent(reprinted::Absent::Unspelled), |again| {
            Maybe::Present(again.to_string())
        })
    }

    /// The value the declaration [`REPRINTED`] of `source` runs to, spelled as
    /// a run spells it.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the source is read under; `source`
    ///   is the text the table's unit lays out, the declaration appended.
    /// - ensures: the run's spelling when the source, lowered in the table's
    ///   unit and judged from where its own text starts, settles as a whole and
    ///   the declaration runs to a value; [`reprinted::Absent::Unlowered`] when
    ///   the source is refused or faults, [`reprinted::Absent::Unrun`] when no
    ///   declaration is [`REPRINTED`] or its run reaches no value.
    /// - provides: the run half of [`Self::reprint_value`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reprint_value`].
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    /// - witness: `typed::tests::an_importer_s_value_reads_back_beside_its_sibling_552`
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    fn run_reprinted(
        &self,
        grammar: &Pbg,
        source: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        let Ok(Composed::Settled { mut program, .. }) =
            lower_unit_source(grammar, source, &self.unit, &mut LoweringCount::default()).and_then(
                |lowering| {
                    judge_lowering(
                        CorpusRoot::Fixture,
                        (lowering, source),
                        &HostGrant::UNBOUNDED,
                        self.base,
                    )
                },
            )
        else {
            return Maybe::Absent(reprinted::Absent::Unlowered);
        };
        let Maybe::Present(last) = program.target()
        else {
            return Maybe::Absent(reprinted::Absent::Unrun);
        };
        let constant = (0_usize ..= usize::from(last))
            .map(ConstantIndex::from)
            .find(|&constant| {
                matches!(program.name(constant), Maybe::Present(held) if held.as_ref() == REPRINTED)
            });
        match constant.map(|constant| program.evaluate(constant)) {
            Some(Evaluation::Value(value)) => Maybe::Present(value.presentation().to_string()),
            Some(
                Evaluation::Sealed(_)
                | Evaluation::Blamed(_)
                | Evaluation::Stuck(_)
                | Evaluation::Unfinished(_)
                | Evaluation::Unrunnable(_),
            )
            | None => Maybe::Absent(reprinted::Absent::Unrun),
        }
    }
}

/// The name of the declaration [`TypeTable::reprint_value`] appends to a
/// source to read a printed value back.
const REPRINTED: &str = "reprinted_value";

/// A match's scrutinee as the typed run found it: its first type, and where
/// it stands, so a pattern typed from it is read under the same binders.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scrutinised
{
    /// The scrutinee's first kept type.
    ty: ValueTypeId,
    /// The declaration whose run typed it, and the scrutinee itself.
    within: Within,
}

quenchant_shape::reason_enum! {
    /// Why a constructor pattern's name has no type of its own.
    mod named {
        /// The reason the name answers nothing apart from its pattern.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The pattern matches at no data family the module declares, or
            /// it names no constructor of it.
            Undeclared,
        }
    }
}

/// Every written span of every match of `module` whose scrutinee the typed run
/// typed, each at what it answers, where it stands, and the spans of the
/// earlier parts it stands under.
///
/// # Specification
/// - requires: `arena` is the one `module` was lowered into and `scrutinised`
///   holds the first kept type of each match's scrutinee, keyed by the
///   scrutinee's syntax node.
/// - ensures: for each match whose scrutinee is in `scrutinised` at a type
///   other than the unknown one, each root pattern at the scrutinee's type and
///   each part at the type its place gives it — a data constructor's field at
///   the field's type, its parameters read at the family's arguments; a word
///   pattern's rest at the word's type; a product's, a pair's and a sum's
///   components at their own; a record pattern's fields at the record type's
///   field of the label each binds; a dependent pair's first at its own and its
///   second at its own, read under the first — and each span the lowering kept
///   for a typed pattern: one read as the pattern at that type, one read as a
///   constructor's name at the constructor's type, which takes the fields to
///   the family as a thunked function and is the family itself for a
///   constructor of no field. A scrutinee the recursion staged is read at the
///   type its stage refines, as the surface writes no stage. A pattern's parts
///   are read off its type's head: a decode of a defined code or a static redex
///   is read as the decode of what it reduces to, as the checker read it, while
///   the pattern itself answers at its type as judged. A part whose type names
///   a part before it — a data constructor's field, a dependent pair's second —
///   is read under those parts, each written as a binder, and so is every part
///   inside it; a span carries the spans of every binder its type stands under,
///   outermost first. A span under an earlier part not written as a binder
///   answers nothing. A part whose place no rule above types, and every span
///   inside it, answers nothing. Each constructor name read at a data family's
///   type is pushed onto `constructed` with the family's constant and the
///   constructor's tag.
/// - provides: the pattern half of [`TypeTable::of`], and the constructor names
///   its referents read.
/// - fails: never; an untyped pattern answers nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a word pattern's empty word, letter, cons and rest, a
///   data constructor pattern's name and field, in a declaration the run
///   settled and in one it refused, and a constructor pattern on a staged
///   scrutinee, are asserted at their types; and a record pattern inside a
///   dependent pair's second component, at its type under the first; a
///   constructor pattern's name refers to the constructor it names, over the
///   name's own bytes; a match on a comparison written as its scrutinee types
///   its patterns at what the comparison returns.
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
/// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
/// - witness: `typed::tests::a_pattern_inside_a_dependent_pair_s_second_component_answers_558`
/// - witness: `typed::tests::an_unused_part_of_a_static_application_answers_1080`
/// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
/// - witness: `typed::tests::a_pattern_on_a_computed_scrutinee_answers_1141`
/// - witness: `typed::tests::a_name_ends_where_it_is_written`
#[spec(ensures: |ret| ret.iter().all(|&(_, ty, _, _)| arena.value_type(ty).is_some()))]
fn matched(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
    definitions: &CodeDefinitions,
    scrutinised: &BTreeMap<NodeIndex, Scrutinised>,
    constructed: &mut Vec<(ByteSpan, ConstantIndex, ConstructorTag)>,
) -> Vec<(ByteSpan, ValueTypeId, Within, Vec<ByteSpan>)>
{
    let mut signatures: BTreeMap<ConstantIndex, &DataSignature> = BTreeMap::new();
    for declaration in module.declarations() {
        if let DeclarationOutcome::Data(index) = declaration.outcome()
            && let Maybe::Present(signature) = module.data(index)
        {
            let _first = signatures.insert(declaration.constant(), signature);
        }
    }
    let mut matched = Vec::new();
    // Each pattern's type, and for a part, the pattern it stands inside with
    // how many of that pattern's parts its type stands under.
    let mut typed: BTreeMap<PatternId, (ValueTypeId, Inside)> = BTreeMap::new();
    let mut pending: Vec<(PatternId, ValueTypeId, Inside)> = Vec::new();
    let mut labelled: BTreeMap<PatternId, &[FieldLabel]> = BTreeMap::new();
    for (_, case) in module.origins().cases() {
        let Some(&Scrutinised { ty, within }) = scrutinised.get(&case.scrutinee)
        else {
            continue;
        };
        // A recursion's stage refines its scrutinee's type without renaming
        // the family, whose constructors the patterns name.
        let ty = match arena.value_type(ty) {
            Some(&ValueType::Staged { base, .. }) => base,
            Some(_) | None => ty,
        };
        if matches!(arena.value_type(ty), None | Some(&ValueType::Unknown)) {
            continue;
        }
        typed.clear();
        pending.clear();
        pending.extend(case.arms.iter().map(|arm| (arm.pattern, ty, None)));
        labelled.clear();
        labelled.extend(
            case.labelled
                .iter()
                .map(|&(held, ref labels)| (held, labels.as_slice())),
        );
        while let Some((pattern, ty, under)) = pending.pop() {
            if typed.insert(pattern, (ty, under)).is_some() {
                continue;
            }
            if let Some(shape) = case.patterns.pattern(pattern) {
                let head = exposed(arena, definitions, ty);
                let labels = labelled.get(&pattern).copied();
                pending.extend(
                    parts(arena, &signatures, shape, labels, head)
                        .into_iter()
                        .map(|(part, part_ty, before)| (part, part_ty, Some((pattern, before)))),
                );
            }
        }
        'spans: for written in &case.spans {
            let Some(&(ty, under)) = typed.get(&written.pattern)
            else {
                continue;
            };
            if written.reading == PatternReading::Constructor
                && let Some(&Pattern::Constructor { tag, .. }) =
                    case.patterns.pattern(written.pattern)
                && let Some(&ValueType::Data { declaration, .. }) = arena.value_type(ty)
            {
                constructed.push((written.span, declaration, tag));
            }
            // The binders the type stands under, gathered innermost first
            // from each pattern around the part.
            let mut earlier = Vec::new();
            let mut inside = under;
            while let Some((parent, before)) = inside {
                let Some(shape) = case.patterns.pattern(parent)
                else {
                    continue 'spans;
                };
                for &field in preceding(shape, before).iter().rev() {
                    let named = match case.patterns.pattern(field) {
                        Some(&Pattern::Binder) => case.spans.iter().find(|held| {
                            held.pattern == field && matches!(held.reading, PatternReading::Matched)
                        }),
                        Some(_) | None => None,
                    };
                    let Some(held) = named
                    else {
                        continue 'spans;
                    };
                    earlier.push(held.span);
                }
                inside = typed.get(&parent).and_then(|&(_, around)| around);
            }
            earlier.reverse();
            let answered = match written.reading {
                PatternReading::Matched => ty,
                PatternReading::Constructor => {
                    let Some(shape) = case.patterns.pattern(written.pattern)
                    else {
                        continue;
                    };
                    match constructor(arena, &signatures, shape, ty) {
                        Maybe::Present(constructor) => constructor,
                        Maybe::Absent(named::Absent::Undeclared) => continue,
                    }
                },
            };
            matched.push((written.span, answered, within, earlier));
        }
    }
    matched
}

/// The head `ty` reads at once the codes it decodes are reduced: a decode
/// of a defined code or of a static redex read as the decode of its reduct,
/// again, until its code takes no step.
///
/// # Specification
/// - requires: `ty` is a type of `arena`, and `definitions` the bodies the
///   typed run unfolded codes by.
/// - ensures: `ty` itself unless it decodes a code [`CodeDefinitions::reduce`]
///   takes a step at; otherwise the decode of the step's reduct at the same
///   level, read again. A code whose step faults is read as it stands.
/// - provides: the former a pattern's parts are read off, as the checker's weak
///   head reads it.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` below takes one step per turn, not recursion.
/// - measure: the static normal form's distance: each step reduces a δ- or
///   β-redex of a code the typed run formed, as the checker's weak head does.
///
/// # Adequacy
/// - hypothesis: L3 — a pattern on a scrutinee at a static application of a
///   defined family reads its parts at the product the application reduces to.
/// - witness: `typed::tests::an_unused_part_of_a_static_application_answers_1080`
#[spec(ensures: |ret| arena.value_type(ret).is_some() || ret == ty)]
fn exposed(
    arena: &mut CoreArena,
    definitions: &CodeDefinitions,
    ty: ValueTypeId,
) -> ValueTypeId
{
    let mut head = ty;
    loop {
        let Some(&ValueType::Element { code, ref target }) = arena.value_type(head)
        else {
            return head;
        };
        let target = target.clone();
        let Ok(Maybe::Present(step)) = definitions.reduce(arena, code)
        else {
            return head;
        };
        head = arena.value_type_element(step.reduct(), target);
    }
}

/// The parts of `pattern`, matched at `ty`, each at the type its place gives
/// it and the number of earlier parts that type stands under; `labels` are the
/// labels a record pattern binds, one per part.
///
/// # Specification
/// - requires: `ty` is a type of `arena` and `signatures` the module's data
///   families by constant.
/// - ensures: as [`matched`] types the parts of one pattern; none for a pattern
///   whose place it does not type, and none for a leaf. A record pattern's
///   parts at a record type are each at the field of its label, or none when a
///   label names no field. A part stands under no earlier part unless its type
///   names one: a data constructor's field whose type names a field before it
///   stands under every field before it at its declared type, and a dependent
///   pair's second whose type names the first stands under the first.
/// - provides: one step of [`matched`]'s walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`], and a record pattern over a product of
///   three and an indexed pattern over a sum of two, each part at its
///   component, and a record pattern over a plain record, labelled and by
///   position, each part at its label's field.
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
/// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
/// - witness: `typed::tests::a_pattern_inside_a_dependent_pair_s_second_component_answers_558`
/// - witness: `typed::tests::a_part_of_a_product_or_a_binary_sum_answers_at_its_component`
/// - witness: `typed::tests::an_unused_part_of_a_static_application_answers_1080`
/// - witness: `typed::tests::an_unread_binder_of_a_plain_record_answers_at_its_field_1883`
#[spec(ensures: |ret| ret.iter().all(|&(_, part, _)| arena.value_type(part).is_some())
    && (ret.is_empty() || matches!(*pattern, Pattern::Constructor { .. } | Pattern::Pair(..) | Pattern::Injection(..))))]
fn parts(
    arena: &mut CoreArena,
    signatures: &BTreeMap<ConstantIndex, &DataSignature>,
    pattern: &Pattern,
    labels: Option<&[FieldLabel]>,
    ty: ValueTypeId,
) -> Vec<(PatternId, ValueTypeId, Before)>
{
    let at = |components: &[ValueTypeId],
              parts: &[PatternId]|
     -> Vec<(PatternId, ValueTypeId, Before)> {
        if components.len() == parts.len() {
            parts
                .iter()
                .copied()
                .zip(components.iter().copied())
                .map(|(part, component)| (part, component, Before(0_usize)))
                .collect()
        }
        else {
            Vec::new()
        }
    };
    match *pattern {
        Pattern::Constructor { tag, ref fields } => {
            match arena.value_type(ty) {
                Some(&ValueType::Path { .. }) => {
                    return fields
                        .iter()
                        .map(|&field| (field, ty, Before(0_usize)))
                        .collect();
                },
                Some(&ValueType::Product(ref components)) if usize::from(tag) == 0_usize => {
                    return at(components, fields);
                },
                Some(&ValueType::Record(ref record)) if usize::from(tag) == 0_usize => {
                    let Some(labels) = labels
                    else {
                        return Vec::new();
                    };
                    let components: Option<Vec<ValueTypeId>> = labels
                        .iter()
                        .map(|label| record.get(label).copied())
                        .collect();
                    return components.map_or_else(Vec::new, |components| at(&components, fields));
                },
                Some(&ValueType::Sum(ref summands)) => {
                    return match summands.get(usize::from(tag)) {
                        Some(&summand) => at(&[summand], fields),
                        None => Vec::new(),
                    };
                },
                Some(&ValueType::Data { .. }) => {},
                Some(_) | None => return Vec::new(),
            }
            match declared(arena, signatures, tag, ty) {
                // A part is typed outside its constructor where it can be: a
                // field naming one before it is typed under those before it.
                Maybe::Present(declared) if declared.len() == fields.len() => {
                    let mut parts = Vec::with_capacity(fields.len());
                    let mut earlier = Binders::NONE;
                    for (count, (&part, &field)) in fields.iter().zip(&declared).enumerate() {
                        parts.push(match strengthen_value_type(arena, field, earlier) {
                            Maybe::Present(outside) => {
                                (part, outside.settle(arena), Before(0_usize))
                            },
                            Maybe::Absent(_) => (part, field, Before(count)),
                        });
                        earlier = earlier.deeper();
                    }
                    parts
                },
                Maybe::Present(_) | Maybe::Absent(named::Absent::Undeclared) => Vec::new(),
            }
        },
        Pattern::Pair(first, second) => match arena.value_type(ty) {
            Some(&ValueType::Product(ref components)) => at(components, &[first, second]),
            Some(&ValueType::Sigma {
                first: component,
                second: later,
            }) => {
                // The second is typed outside the first where it can be.
                let rest = match strengthen_value_type(arena, later, Binders::NONE.deeper()) {
                    Maybe::Present(outside) => (second, outside.settle(arena), Before(0_usize)),
                    Maybe::Absent(_) => (second, later, Before(1_usize)),
                };
                Vec::from([(first, component, Before(0_usize)), rest])
            },
            Some(_) | None => Vec::new(),
        },
        Pattern::Injection(side, body) => match arena.value_type(ty) {
            Some(&ValueType::Sum(ref summands)) if summands.len() == 2_usize => {
                let summand = match side {
                    Side::Left => summands.first(),
                    Side::Right => summands.get(1_usize),
                };
                summand
                    .map(|&summand| (body, summand, Before(0_usize)))
                    .into_iter()
                    .collect()
            },
            Some(_) | None => Vec::new(),
        },
        Pattern::Wildcard
        | Pattern::Binder
        | Pattern::Unit
        | Pattern::Literal(_)
        | Pattern::Hole(_) => Vec::new(),
    }
}

/// The field types of the constructor `tag` of the data family `ty`, its
/// parameters read at the family's arguments.
///
/// # Specification
/// - requires: as [`parts`].
/// - ensures: the constructor's declared fields, in order, each with the
///   family's arguments substituted for its parameters beneath the fields
///   before it, outermost first, as the checker's branch types read them: a
///   telescope over the context `ty` is read in.
/// - provides: what a data constructor pattern's parts and name are typed by.
/// - fails: never; a family the module does not declare, an argument count
///   other than its parameters', or a tag past its constructors answers
///   [`named::Absent::Undeclared`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref fields) => matches!(arena.value_type(ty), Some(&ValueType::Data { declaration, .. })
        if signatures.get(&declaration)
            .and_then(|signature| signature.constructors().get(usize::from(tag)))
            .is_some_and(|written| written.len() == fields.len())),
    Maybe::Absent(named::Absent::Undeclared) => true,
})]
fn declared(
    arena: &mut CoreArena,
    signatures: &BTreeMap<ConstantIndex, &DataSignature>,
    tag: ConstructorTag,
    ty: ValueTypeId,
) -> Maybe<Vec<ValueTypeId>, named::Absent>
{
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(ty)
    else {
        return Maybe::Absent(named::Absent::Undeclared);
    };
    let Some(signature) = signatures.get(&declaration)
    else {
        return Maybe::Absent(named::Absent::Undeclared);
    };
    let (Some(fields), true) = (
        signature.constructors().get(usize::from(tag)),
        signature.parameters().len() == arguments.len(),
    )
    else {
        return Maybe::Absent(named::Absent::Undeclared);
    };
    let arguments = arguments.clone();
    let mut declared = Vec::with_capacity(fields.len());
    let mut earlier = Binders::NONE;
    for &field in fields {
        let mut subject = field;
        for (index, &argument) in arguments.iter().enumerate().rev() {
            let depth = Binders::from(u32::try_from(index).unwrap_or(u32::MAX));
            let argument = shift_value(arena, argument, depth).settle(arena);
            subject = instantiate_value_type_under(arena, subject, argument, earlier);
        }
        declared.push(subject);
        earlier = earlier.deeper();
    }
    Maybe::Present(declared)
}

/// The type of the constructor `pattern` names, matched at `ty`: from its
/// fields to the family, as a thunked function.
///
/// # Specification
/// - requires: as [`parts`].
/// - ensures: for a constructor pattern at a data family, the family itself
///   when the constructor has no field, and otherwise `U (A₁ → … → F T)` over
///   its fields' telescope, as a data declaration's constructor is described.
/// - provides: what the name of a constructor pattern answers at.
/// - fails: never; any other pattern, or one at a type no data family
///   classifies, answers [`named::Absent::Undeclared`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
#[spec(ensures: |ret| match ret {
    Maybe::Present(answer) => matches!(*pattern, Pattern::Constructor { .. })
        && (answer == ty || matches!(arena.value_type(answer), Some(&ValueType::Thunk(_)))),
    Maybe::Absent(named::Absent::Undeclared) => true,
})]
fn constructor(
    arena: &mut CoreArena,
    signatures: &BTreeMap<ConstantIndex, &DataSignature>,
    pattern: &Pattern,
    ty: ValueTypeId,
) -> Maybe<ValueTypeId, named::Absent>
{
    let &Pattern::Constructor { tag, .. } = pattern
    else {
        return Maybe::Absent(named::Absent::Undeclared);
    };
    let Maybe::Present(fields) = declared(arena, signatures, tag, ty)
    else {
        return Maybe::Absent(named::Absent::Undeclared);
    };
    if fields.is_empty() {
        return Maybe::Present(ty);
    }
    Maybe::Present(constructor_classifier(arena, ty, &fields))
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_grammar::built_in;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Declared;
    use super::ReadSite;
    use super::RoundTrip;
    use super::Subject;
    use super::TypeTable;
    use super::checked_against;
    use super::typing;
    use super::unrefused;

    /// What the table answers at a position, as text.
    #[derive(Debug, Eq, PartialEq)]
    struct Answer
    {
        /// What the node is.
        subject: Subject,
        /// Its type.
        ty: String,
        /// The type it was checked against, when spelled otherwise.
        expected: Maybe<String, checked_against::Absent>,
    }

    /// What `table` answers at the first byte of the first occurrence of
    /// `needle` in `source`, as text; panics when `needle` does not occur.
    ///
    /// # Specification
    /// trivial.
    fn answer(
        table: &TypeTable,
        source: SourceText<'_>,
        needle: SourceText<'_>,
    ) -> Maybe<Answer, typing::Absent>
    {
        let offset = <&str>::from(source)
            .find(<&str>::from(needle))
            .expect("the needle occurs");
        match table.at(
            ByteOffset::from(offset),
            PageWidth::from(80_u32),
            Form::Explicit.into(),
        ) {
            Maybe::Present(entry) => Maybe::Present(Answer {
                subject: entry.subject(),
                ty: String::from(entry.ty().as_ref()),
                expected: match entry.expected() {
                    Maybe::Present(expected) => Maybe::Present(String::from(expected.as_ref())),
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                },
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The table [`TypeTable::of`] builds for `source`; panics when the grammar
    /// or the parse fails.
    ///
    /// # Specification
    /// trivial.
    fn table(source: SourceText<'_>) -> TypeTable
    {
        let grammar = built_in().expect("the built-in grammar builds");
        TypeTable::of(&grammar, source).expect("the source parses")
    }

    /// #1743: a parameter nothing reads answers as a binder at its own type,
    /// not at the type of the lambda written at its name that opens it.
    #[test]
    fn an_unused_parameter_answers_at_its_own_type_1743()
    {
        let source = SourceText::from(
            "def plus(n : Integer, m : Integer) -> -F Integer { return n }\n\ndef keep(a : \
             Type, x : a) -> -F Type { return a }\n",
        );
        let table = table(source);
        for (needle, ty, reason) in [
            ("n :", "Integer", "a parameter its body reads"),
            (
                "m :",
                "Integer",
                "a parameter nothing reads, not the lambda opening it",
            ),
            (
                "x :",
                "a",
                "an unread parameter whose type names an earlier one",
            ),
        ] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "{reason}"
            );
        }
    }

    /// An answer of `subject` at `ty`, checked against nothing else.
    ///
    /// # Specification
    /// trivial.
    fn agreed(
        subject: Subject,
        ty: SourceText<'_>,
    ) -> Maybe<Answer, typing::Absent>
    {
        Maybe::Present(Answer {
            subject,
            ty: String::from(<&str>::from(ty)),
            expected: Maybe::Absent(checked_against::Absent::Agreed),
        })
    }

    /// Where a referent stands: its source, the offset of its name in that
    /// source's text, and the name as written.
    #[derive(Debug, Eq, PartialEq)]
    struct Site
    {
        /// The unit's source the referent is written in.
        source: gandr_surface_lowering::SourceIndex,
        /// The offset of its name in that source's text.
        at: ByteOffset,
        /// The name as written.
        name: String,
    }

    /// The offset of the first occurrence of `needle` in `source`; panics when
    /// `needle` does not occur.
    ///
    /// # Specification
    /// trivial.
    fn found(
        source: SourceText<'_>,
        needle: SourceText<'_>,
    ) -> ByteOffset
    {
        ByteOffset::from(
            <&str>::from(source)
                .find(<&str>::from(needle))
                .expect("the needle occurs"),
        )
    }

    /// The site of the name `name` written at the first occurrence of
    /// `needle` in `text`, the text of the unit's first source.
    ///
    /// # Specification
    /// trivial.
    fn site(
        text: SourceText<'_>,
        needle: SourceText<'_>,
        name: SourceText<'_>,
    ) -> Site
    {
        Site {
            source: gandr_surface_lowering::SourceIndex::from(0_usize),
            at: found(text, needle),
            name: String::from(<&str>::from(name)),
        }
    }

    /// Where the referent `table` answers at the first byte of the first
    /// occurrence of `needle` in `source` stands.
    ///
    /// # Specification
    /// trivial.
    fn refers(
        table: &TypeTable,
        source: SourceText<'_>,
        needle: SourceText<'_>,
    ) -> Option<Site>
    {
        let Maybe::Present((_, referent)) = table.referent(found(source, needle))
        else {
            return None;
        };
        written(table, referent)
    }

    /// Where `referent` stands.
    ///
    /// # Specification
    /// trivial.
    fn written(
        table: &TypeTable,
        referent: super::Referent,
    ) -> Option<Site>
    {
        let named = referent.named();
        let text = <&str>::from(table.source_text(referent.source())?);
        let name = text.get(usize::from(named.start()) .. usize::from(named.end()))?;
        Some(Site {
            source: referent.source(),
            at: named.start(),
            name: String::from(name),
        })
    }

    /// The source the referent witnesses read: a family, a function matching
    /// on it, and a numeral built of its constructors.
    const REFERRED: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
                            def rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero \
                            => n,\n    Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef two : Nat ;\n\
                            def two = Succ(Succ(Zero)) ;";

    /// #1129: an `ext` member's keyword holds none of the members it
    /// generates, neither a binder nor a law's orientation, and the face and
    /// the boundary constant it writes refer to the face and the constant.
    #[test]
    fn an_ext_member_names_its_face_and_boundary_1129()
    {
        let source = SourceText::from(include_str!(
            "../../surface-corpus/fixture/model/extension/generated.gandr"
        ));
        let table = table(source);
        let keyword = found(source, SourceText::from("ext Cell = Val on left is zero;"));
        assert!(
            !matches!(
                answer(
                    &table,
                    source,
                    SourceText::from("ext Cell = Val on left is zero;")
                ),
                Maybe::Present(Answer {
                    subject: Subject::Binder,
                    ..
                })
            ),
            "the keyword answers no generated operation"
        );
        assert!(
            table
                .orientations()
                .iter()
                .all(|&(span, _)| span.start() != keyword),
            "the keyword notes no generated law's direction"
        );
        let at = |needle: &'static str| refers(&table, source, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                source,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        assert_eq!(
            at("left is zero;\n  oper c"),
            named("left = {0}", "left"),
            "the face names the shape's face"
        );
        assert_eq!(
            at("zero;\n  oper c"),
            named("zero : Val", "zero"),
            "the boundary names the constant"
        );
    }

    /// #1128: in theory blocks and module ascriptions each name refers to its
    /// own declaration — an included theory, an ascribed one, a member its
    /// rule or operation writes — and no referent covers a block whole.
    #[test]
    fn theory_names_refer_to_their_own_declarations_1128()
    {
        let source = SourceText::from(include_str!(
            "../../surface-corpus/fixture/model/include/monoid.gandr"
        ));
        let table = table(source);
        let at = |needle: &'static str| refers(&table, source, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                source,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        assert_eq!(
            at("include Semigroup;\n  oper one"),
            None,
            "a keyword inside a theory answers nothing, not the block whole"
        );
        assert_eq!(at("rule unitL"), None, "nor does a rule's keyword");
        assert_eq!(
            at("Semigroup;\n  oper one"),
            named("Semigroup {", "Semigroup"),
            "an include names the theory it includes"
        );
        assert_eq!(
            at("Monoid) {"),
            named("Monoid {", "Monoid"),
            "a model ascription's argument names the theory, not a member of the module"
        );
        assert_eq!(
            at("mul(one(), x) ==> x;\n  rule unitR"),
            named("mul : (x", "mul"),
            "an operation a rule applies names the operation, here the included one"
        );
        assert_eq!(
            at("M;\n  rule unitL"),
            named("M : Type", "M"),
            "a sort an operation writes names the sort"
        );
    }

    /// #795: each written use answers the site of what it names — a binder,
    /// a declaration, a family, a constructor in a term and in a pattern — and
    /// a position in no use answers nothing.
    #[test]
    fn a_use_refers_to_its_binder_and_its_declaration_795()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let at = |needle: &'static str| refers(&table, referred, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                referred,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        assert_eq!(
            at("m {"),
            named("m : Nat)", "m"),
            "a parameter's use, its binder"
        );
        assert_eq!(
            at("n,\n"),
            named("n : Nat,", "n"),
            "the other parameter's use, its binder"
        );
        assert_eq!(
            at("p))"),
            named("p) =>", "p"),
            "a pattern variable's use, its pattern"
        );
        assert_eq!(
            at("plus[<]"),
            named("plus(n", "plus"),
            "a declaration's use, its name"
        );
        assert_eq!(
            at("Succ(plus"),
            named("Succ : (n", "Succ"),
            "a constructor in a term, its name in the family"
        );
        assert_eq!(
            at("Succ(p)"),
            named("Succ : (n", "Succ"),
            "a constructor in a pattern, its name in the family"
        );
        assert_eq!(
            at("Zero))"),
            named("Zero : Nat", "Zero"),
            "a constructor inside another's argument answers itself"
        );
        assert_eq!(
            at("Nat ;"),
            named("Nat : Type", "Nat"),
            "a written family, its declaration"
        );
        assert_eq!(at("case"), None, "a keyword refers to nothing");
        assert_eq!(at("m : Nat)"), None, "a binder is no use of itself");
    }

    #[test]
    fn the_uses_within_a_range_answer_whole()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let text = <&str>::from(referred);
        let named = |span: ByteSpan| {
            String::from(
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default(),
            )
        };
        let within = |needle: &str| {
            let start = text.find(needle).expect("the needle occurs");
            let span = ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(needle.len())),
            )
            .expect("an ordered span");
            table
                .uses_within(span)
                .map(|(used, referent)| (named(used), named(referent.named())))
                .collect::<Vec<_>>()
        };
        let pair = |used: &str, at: &str| (String::from(used), String::from(at));
        assert_eq!(
            within("Succ(plus[<](n, p))"),
            [
                pair("Succ", "Succ"),
                pair("Succ(plus[<](n, p))", "Succ"),
                pair("plus", "plus"),
                pair("plus[<]", "plus"),
                pair("n", "n"),
                pair("p", "p")
            ],
            "each use the index keeps, a call's whole application and its staged head beside their names, in order"
        );
        assert_eq!(
            within("Succ(pl"),
            [pair("Succ", "Succ")],
            "a name the range cuts is not answered"
        );
    }

    /// #1371: the words a loop presents are minted at its data declaration
    /// and written nowhere in it, so no name the declaration writes refers to
    /// the loop's point; each side of the loop writes the point, and refers to
    /// it.
    #[test]
    fn a_loop_s_words_are_written_nowhere_in_its_declaration_1371()
    {
        let source = SourceText::from(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\ndef wound(p : \
             Path(Circle, Base, Base)) -> -F Circle {\n  return Base\n}\n",
        );
        let table = table(source);
        let at = |needle: &'static str| refers(&table, source, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                source,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        for declared in ["Circle : Type", "Base : Circle", "loop : Base"] {
            assert_eq!(at(declared), None, "a declared name `{declared}` is no use");
        }
        assert_eq!(
            at("Circle;"),
            named("Circle : Type", "Circle"),
            "the point's result, its family"
        );
        assert_eq!(
            at("Base <-> Base"),
            named("Base : Circle", "Base"),
            "the loop's source, the point it writes"
        );
        assert_eq!(
            at("Base;\n}"),
            named("Base : Circle", "Base"),
            "the loop's target, the point it writes"
        );
        assert_eq!(
            at("Circle, Base"),
            named("Circle : Type", "Circle"),
            "a use of the family outside its declaration"
        );
        assert_eq!(
            at("Base\n}"),
            named("Base : Circle", "Base"),
            "a use of the point outside its declaration"
        );
    }

    /// #1360: a constructor's result names its family, and each of the
    /// result's arguments what it names, as a field's type does.
    #[test]
    fn a_constructor_s_result_names_its_family_1360()
    {
        let source = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndata Vec(a : \
             Type) : Nat -> Type {\n  VNil : Vec(a, Zero);\n  VCons : (n : Nat, head : a, tail \
             : Vec(a, n)) --> Vec(a, Succ(n));\n}\n",
        );
        let table = table(source);
        let at = |needle: &'static str| refers(&table, source, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                source,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        assert_eq!(
            at("Nat;\n  Succ"),
            named("Nat : Type", "Nat"),
            "a constant constructor's result, its family"
        );
        assert_eq!(
            at("Nat;\n}"),
            named("Nat : Type", "Nat"),
            "a constructor's result after its fields, its family"
        );
        assert_eq!(
            at("Vec(a, Zero)"),
            named("Vec(a : Type)", "Vec"),
            "an indexed constructor's result, its family"
        );
        assert_eq!(
            at("Vec(a, Succ(n));"),
            named("Vec(a : Type)", "Vec"),
            "an indexed result after its fields, its family"
        );
        assert_eq!(
            at("Zero);"),
            named("Zero : Nat", "Zero"),
            "a result's index, the constructor it writes"
        );
        assert_eq!(
            at("Succ(n));"),
            named("Succ : (n", "Succ"),
            "a result's index applying a constructor, that constructor"
        );
        assert_eq!(
            at("a, Zero"),
            named("a : Type", "a"),
            "a result's argument repeating a parameter, the parameter's binder"
        );
    }

    /// #836: a constructor applied to no field yet refuses its declaration,
    /// and its name still refers to the constructor.
    #[test]
    fn a_refused_declaration_s_uses_refer_to_their_sites_836()
    {
        let typing = REFERRED.replace("Succ(Succ(Zero))", "Succ()");
        let referred = SourceText::from(typing.as_str());
        let table = table(referred);
        assert_eq!(
            refers(&table, referred, SourceText::from("Succ()")),
            Some(site(
                referred,
                SourceText::from("Succ : (n"),
                SourceText::from("Succ"),
            )),
            "the constructor's name in the family, though `two` is refused"
        );
    }

    /// #859: a recursive call's leading argument, which the call erases,
    /// refers to the parameter it passes unchanged.
    #[test]
    fn a_recursive_call_s_leading_argument_refers_to_its_parameter_859()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        assert_eq!(
            refers(&table, referred, SourceText::from("n, p)")),
            Some(site(
                referred,
                SourceText::from("n : Nat,"),
                SourceText::from("n"),
            )),
            "the leading `n` of `plus[<](n, p)`, the parameter `n`"
        );
    }

    /// A name is found at its declaring name with every use referring to it:
    /// a parameter, a pattern variable, a declaration and a constructor in
    /// terms and in a pattern; a use is no declaring name.
    #[test]
    fn each_name_is_found_with_every_use_referring_to_it()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let at = |needle: &'static str| found(referred, SourceText::from(needle));
        let uses = |needle: &'static str| -> Vec<ByteOffset> {
            let Maybe::Present(referent) = table.named_at(at(needle))
            else {
                return Vec::new();
            };
            table
                .uses_of(referent.source(), referent.named())
                .map(super::ByteSpan::start)
                .collect()
        };
        assert_eq!(
            uses("n : Nat,"),
            [at("n,\n"), at("n, p)")],
            "a parameter: its use in an arm and in the recursive call"
        );
        assert_eq!(
            uses("m : Nat)"),
            [at("m {")],
            "the other parameter: its one use"
        );
        assert_eq!(
            uses("p) =>"),
            [at("p))")],
            "a pattern variable: its one use"
        );
        assert_eq!(
            uses("plus(n"),
            [at("plus[<]")],
            "a declaration: its recursive call"
        );
        assert_eq!(
            uses("Succ : (n"),
            [
                at("Succ(p)"),
                at("Succ(plus"),
                at("Succ(Succ"),
                at("Succ(Zero")
            ],
            "a constructor: in a pattern and in terms, nested ones included"
        );
        assert!(
            matches!(table.named_at(at("m {")), Maybe::Absent(_)),
            "a use is no declaring name"
        );
    }

    /// #1034: a name declared in two halves answers each half at its own
    /// site, and its second half's name is a use of it, found with the others.
    #[test]
    fn each_half_of_a_declaration_answers_its_own_site_1034()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let at = |needle: &'static str| found(referred, SourceText::from(needle));
        let named = |needle: &'static str, name: &'static str| {
            Some(site(
                referred,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        let Maybe::Present(two) = table.named_at(at("two : Nat"))
        else {
            panic!("the signature's name declares `two`");
        };
        assert_eq!(
            written(&table, table.half(two, super::DeclaredHalf::Signature)),
            named("two : Nat", "two"),
            "the signature half, at the signature's name"
        );
        assert_eq!(
            written(&table, table.half(two, super::DeclaredHalf::Definition)),
            named("two = Succ", "two"),
            "the definition half, at the definition's name"
        );
        assert_eq!(
            refers(&table, referred, SourceText::from("two = Succ")),
            named("two : Nat", "two"),
            "the definition's name refers to the declaration"
        );
        assert_eq!(
            table
                .uses_of(two.source(), two.named())
                .map(super::ByteSpan::start)
                .collect::<Vec<_>>(),
            [at("two = Succ")],
            "the definition's name is found with the declaration's uses"
        );
        let Maybe::Present(plus) = table.named_at(at("plus(n"))
        else {
            panic!("the function's name declares `plus`");
        };
        assert_eq!(
            table.half(plus, super::DeclaredHalf::Signature),
            plus,
            "a function written once answers itself"
        );
    }

    /// #795: the type of a node answers the families it names, and a written
    /// family answers itself.
    #[test]
    fn a_use_s_type_refers_to_the_families_it_names_795()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let at = |needle: &'static str| {
            table
                .type_referents(found(referred, SourceText::from(needle)))
                .into_iter()
                .filter_map(|referent| written(&table, referent))
                .collect::<Vec<_>>()
        };
        let nat = Vec::from([site(
            referred,
            SourceText::from("Nat : Type"),
            SourceText::from("Nat"),
        )]);
        assert_eq!(at("m {"), nat, "a parameter's use, at its type's family");
        assert_eq!(
            at("plus[<]"),
            nat,
            "a function's use, at the family its type names"
        );
        assert_eq!(at("Nat ;"), nat, "a written family, at itself");
        assert_eq!(at("\ndef two : Nat"), Vec::new(), "no node, no family");
    }

    /// #1441: the type a use is presented at links each family name it
    /// writes to the family's declaration, at the bytes of that name; the
    /// binders it names are not listed.
    #[test]
    fn a_presented_type_links_each_name_it_writes_1441()
    {
        let referred = SourceText::from(REFERRED);
        let table = table(referred);
        let Maybe::Present(typed) = table.at(
            found(referred, SourceText::from("plus[<]")),
            PageWidth::from(80_u32),
            Form::Sugared.into(),
        )
        else {
            panic!("the recursive call's head is typed");
        };
        let presented = typed.ty();
        let text: &str = presented.as_ref();
        let linked: Vec<(Option<&str>, Option<Site>)> = table
            .written_referents(presented)
            .into_iter()
            .map(|(name, referent)| {
                let start = usize::try_from(u64::from(name.start())).expect("a byte");
                let end = usize::try_from(u64::from(name.end())).expect("a byte");
                (text.get(start .. end), written(&table, referent))
            })
            .collect();
        let nat = (
            Some("Nat"),
            Some(site(
                referred,
                SourceText::from("Nat : Type"),
                SourceText::from("Nat"),
            )),
        );
        assert!(!linked.is_empty(), "the type names its family: {text:?}");
        assert_eq!(
            linked.len(),
            text.matches("Nat").count(),
            "each `Nat` of {text:?} is listed"
        );
        assert!(
            linked.iter().all(|entry| *entry == nat),
            "each `Nat` of {text:?}, at the family's declaration: {linked:?}"
        );
    }

    /// #795: a name a sibling declares refers to the sibling's own text.
    #[test]
    fn an_imported_name_refers_to_its_sibling_795()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let sibling = SourceText::from(
            "data Point : Type {\n  Here : Point;\n}\ndef here : Point ;\ndef here = Here ;",
        );
        let importer =
            SourceText::from("import \"./point.gandr\" ;\ndef there : Point ;\ndef there = here ;");
        let laid = format!("{}\n{}", <&str>::from(sibling), <&str>::from(importer));
        let base = ByteOffset::from(<&str>::from(sibling).len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        assert_eq!(
            usize::from(table.own_source()),
            1_usize,
            "the importer is the unit's last"
        );
        let at = |needle: &'static str| refers(&table, importer, SourceText::from(needle));
        let in_sibling = |needle: &'static str, name: &'static str| {
            Some(site(
                sibling,
                SourceText::from(needle),
                SourceText::from(name),
            ))
        };
        assert_eq!(
            at("here ;"),
            in_sibling("here : Point", "here"),
            "the sibling's declaration, in the sibling's own text"
        );
        assert_eq!(
            at("Point ;"),
            in_sibling("Point : Type", "Point"),
            "the sibling's family, in the sibling's own text"
        );
        assert_eq!(
            at("there = "),
            Some(Site {
                source: SourceIndex::from(1_usize),
                at: found(importer, SourceText::from("there : Point")),
                name: String::from("there"),
            }),
            "the importer's definition half's name, at its signature (#1034)"
        );
    }

    /// #806: every name a unit declares is offered once, with what it names:
    /// a sibling's family, its constructor and its function, and the
    /// importer's own declaration.
    #[test]
    fn the_declared_names_are_named_with_their_kind_806()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        use super::NameKind;

        let sibling = SourceText::from(
            "data Point : Type {\n  Here : Point;\n  There : Point;\n}\ndef here : Point ;\ndef \
             here = Here ;",
        );
        let importer =
            SourceText::from("import \"./point.gandr\" ;\ndef there : Point ;\ndef there = here ;");
        let laid = format!("{}\n{}", <&str>::from(sibling), <&str>::from(importer));
        let base = ByteOffset::from(<&str>::from(sibling).len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        let named: Vec<(Site, NameKind)> = table
            .declared_names()
            .iter()
            .filter_map(|&(referent, kind)| Some((written(&table, referent)?, kind)))
            .collect();
        let in_source =
            |text: SourceText<'_>, source: usize, needle: &'static str, name: &'static str| Site {
                source: SourceIndex::from(source),
                at: found(text, SourceText::from(needle)),
                name: String::from(name),
            };
        assert_eq!(
            named,
            [
                (
                    in_source(sibling, 0, "Point : Type", "Point"),
                    NameKind::Family
                ),
                (
                    in_source(sibling, 0, "Here : Point", "Here"),
                    NameKind::Constructor
                ),
                (
                    in_source(sibling, 0, "There : Point", "There"),
                    NameKind::Constructor
                ),
                (
                    in_source(sibling, 0, "here : Point ;", "here"),
                    NameKind::Value
                ),
                (
                    in_source(importer, 1, "there : Point", "there"),
                    NameKind::Value
                ),
            ],
            "each declared name once, in the order the unit writes them, with its kind"
        );
    }

    /// A term name and a type head that nothing declares are each kept where
    /// they are written, and a declaration whose names resolve keeps nothing.
    #[test]
    fn a_name_nothing_declares_is_kept_where_it_is_written()
    {
        let source = SourceText::from(
            "def a : Integer ;\ndef a = nope ;\ndef b : Natural ;\ndef c : Integer ;\ndef c = 1 ;",
        );
        let table = table(source);
        let spelled: Vec<&str> = table
            .unresolved()
            .iter()
            .filter_map(|span| {
                <&str>::from(source).get(usize::from(span.start()) .. usize::from(span.end()))
            })
            .collect();
        assert_eq!(
            spelled,
            ["nope", "Natural"],
            "each name nothing answers, at its own spelling, in order"
        );
    }

    /// A name nothing declares is kept between two declarations refused as
    /// shadowing an import: only a refused form's own bytes are set aside,
    /// not those before or after it.
    #[test]
    fn a_name_nothing_declares_is_kept_beside_a_form_refused_as_shadowing()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let sibling = "data Point : Type {\n  Here : Point;\n}\ndata Spot : Type {\n  There : \
                       Spot;\n}";
        let importer = "import \"./point.gandr\" ;\ndata Point : Type {\n  Here : Point;\n}\ndef \
                        a : Integer ;\ndef a = nope ;\ndata Spot : Type {\n  There : Spot;\n}";
        let laid = format!("{sibling}\n{importer}");
        let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        let spelled: Vec<&str> = table
            .unresolved()
            .iter()
            .filter_map(|span| importer.get(usize::from(span.start()) .. usize::from(span.end())))
            .collect();
        assert_eq!(
            spelled,
            ["nope"],
            "the unknown name between the refused forms is kept: {:?}",
            table.unresolved()
        );
    }

    /// #831: the binders in scope at an offset of the source's own text are
    /// spelled from that text, the declaration being typed refused, and each
    /// is placed where that text writes its name.
    #[test]
    fn the_binders_in_scope_are_spelled_in_the_source_s_text_831()
    {
        let typing = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec plus(n : \
             Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    Succ(p) => Succ(pl)\n  \
             }\n}\n",
        );
        let table = table(typing);
        let at = |needle: &'static str| {
            table
                .binders_at(found(typing, SourceText::from(needle)))
                .map(|(name, site)| {
                    assert_eq!(
                        <&str>::from(typing)
                            .get(usize::from(site.start()) .. usize::from(site.end())),
                        Some(<&str>::from(name)),
                        "a binder is placed at its written name"
                    );
                    String::from(<&str>::from(name))
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            table
                .binders_at(found(typing, SourceText::from("pl)")))
                .map(|(_, site)| site.start())
                .collect::<Vec<_>>(),
            ["p) =>", "m : Nat)", "plus(", "n : Nat,"]
                .map(|needle| found(typing, SourceText::from(needle))),
            "each binder at its own written name, the arm's before the function's"
        );
        assert_eq!(
            at("pl)"),
            ["p", "m", "plus", "n"],
            "the arm's binder, then the function's"
        );
        assert_eq!(
            at("n,\n"),
            ["m", "plus", "n"],
            "a sibling arm never sees `p`"
        );
        assert_eq!(
            at("Nat;"),
            Vec::<String>::new(),
            "a family's constructor reads under no binder"
        );
    }

    #[test]
    fn an_imported_name_types_at_its_use()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let sibling =
            "data Point : Type {\n  Here : Point;\n}\ndef here : Point ;\ndef here = Here ;";
        let importer =
            SourceText::from("import \"./point.gandr\" ;\ndef there : Point ;\ndef there = here ;");
        let laid = format!("{sibling}\n{}", <&str>::from(importer));
        let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        let at = |needle: &'static str| answer(&table, importer, SourceText::from(needle));
        assert_eq!(
            at("here ;"),
            agreed(Subject::Term, SourceText::from("Point")),
            "the sibling's definition types at its use, at the importer's own offset"
        );
        assert_eq!(
            at("Point ;"),
            agreed(Subject::Type, SourceText::from("Type")),
            "the sibling's family is a written type in the importer"
        );
        assert!(
            table
                .spans()
                .all(|span| usize::from(span.end()) <= <&str>::from(importer).len()),
            "no entry of the sibling is kept"
        );
    }

    /// #1365: a table over an importer's unit keeps the documentation each
    /// source writes of itself under that source, the sibling's and the
    /// importer's apart, and none for a source writing none.
    #[test]
    fn the_table_keeps_each_source_s_own_documentation_1365()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let grammar = built_in().expect("the built-in grammar builds");
        let kept = |sibling: &str, importer: &str| {
            let laid = format!("{sibling}\n{importer}");
            let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
            let unit = Unit::new(vec![
                UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
                UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
            ])
            .expect("the unit's sources start in order");
            let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
                .expect("the unit parses");
            [0_usize, 1_usize].map(|source| {
                match table.source_documentation(SourceIndex::from(source)) {
                    Maybe::Present(text) => Some(String::from(text.as_ref())),
                    Maybe::Absent(_) => None,
                }
            })
        };
        assert_eq!(
            kept(
                "//! Points.\ndata Point : Type {\n  Here : Point;\n}",
                "//! Uses [Point].\nimport \"./point.gandr\" ;\ndef there : Point ;\ndef there \
                 = Here ;"
            ),
            [
                Some(String::from("Points.")),
                Some(String::from("Uses [Point]."))
            ],
            "each source's own run is kept under it"
        );
        assert_eq!(
            kept(
                "data Point : Type {\n  Here : Point;\n}",
                "//! Uses [Point].\nimport \"./point.gandr\" ;\ndef there : Point ;\ndef there \
                 = Here ;"
            ),
            [None, Some(String::from("Uses [Point]."))],
            "a sibling writing none keeps none, and the importer's stays its own"
        );
    }

    /// #552: a table built over an importer's unit reads its printed values
    /// and types back in that unit. Read alone, the importer's import
    /// resolves to nothing and every declaration of it — the appended probe
    /// among them — is refused with the import.
    #[test]
    fn an_importer_s_value_reads_back_beside_its_sibling_552()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_pretty::Name;

        use super::reprinted;
        use super::signed;

        let sibling = "data Point : Type {\n  Here : Point;\n}";
        let importer = "import \"./point.gandr\" ;\ndef there : +U (-F +{Point, Point}) ;\ndef \
                        there = thunk { return +{.1 = Here} } ;";
        let laid = format!("{sibling}\n{importer}");
        let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        assert_eq!(
            table.reprint_value(
                &grammar,
                Maybe::Absent(signed::Absent::Unsigned),
                SourceText::from("Here")
            ),
            Maybe::Present(String::from("Here")),
            "the sibling's constructor reads back as written"
        );
        assert_eq!(
            table.reprint_value(
                &grammar,
                Maybe::Absent(signed::Absent::Unsigned),
                SourceText::from("nope")
            ),
            Maybe::Absent(reprinted::Absent::Unlowered),
            "an unsigned value the lowering refuses has no signature to run under"
        );
        assert_eq!(
            table.reprint_value(
                &grammar,
                Maybe::Present(Name::from("there")),
                SourceText::from("+{.1 = Here}")
            ),
            Maybe::Present(String::from("+{.1 = Here}")),
            "an injection, which needs its type, reads back run under the declaration's"
        );
        let trips: Vec<(String, RoundTrip)> = table
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        assert!(
            !trips.is_empty() && trips.iter().all(|&(_, ref trip)| *trip == RoundTrip::Equal),
            "every printed type of the importer reads back beside its sibling: {trips:?}"
        );
    }

    /// #669: a `theory`'s stated normal form is a term of the block, which a
    /// top-level thunk cannot name. Read back under the block's rules it is
    /// itself, and a call reads to the normal form the engine spells.
    #[test]
    fn a_theory_s_normal_form_reads_back_under_its_rules_669()
    {
        use gandr_surface_pretty::Name;

        use super::reprinted;

        let source = SourceText::from(
            "theory Pointed {\n  sort P : Type;\n  oper pt : P;\n  oper flip : (p : P) --> P;\n  \
             rule flipPt : flip(pt()) <=> pt();\n  rule flipFlip : flip(flip(p)) <=> p;\n}\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let table = table(source);
        let block = Name::from("Pointed");
        let read = |written: &'static str| {
            table.reprint_normal_form(&grammar, block, SourceText::from(written))
        };
        assert_eq!(read("pt"), Maybe::Present(String::from("pt")), "as written");
        assert_eq!(
            read("flip(flip(pt))"),
            Maybe::Present(String::from("pt")),
            "a call to its normal form"
        );
        assert_eq!(
            table.reprint_normal_form(&grammar, Name::from("Absent"), SourceText::from("pt")),
            Maybe::Absent(reprinted::Absent::Unlowered),
            "no block of that name"
        );
    }

    /// #610: a run value of one member of a component reprints under its own
    /// declaration's signature. The walk numbers the constants of the whole
    /// component — here the base, a sibling that also imports it, then the
    /// member — while the member's table numbers only its import closure, so
    /// the walk's number of `joined` names another declaration of the table,
    /// or none, and the `Cons` that needs its type refused to read back.
    #[test]
    fn a_member_s_value_reprints_under_its_own_declaration_610()
    {
        use core::convert::Infallible;
        use core::ops::ControlFlow;
        use std::path::Path;

        use gandr_kernel_term::ConstantIndex;
        use gandr_surface_pretty::Name;

        use crate::component::lay_out;
        use crate::compose::Composed;
        use crate::evaluate::Evaluation;
        use crate::pool::Pool;
        use crate::walk::Step;
        use crate::walk::Walk;
        use crate::walk::tests::Scratch;
        use crate::width::Width;

        let scratch = Scratch::new(Path::new("member-reprint"));
        scratch.file(
            Path::new("fixture/base.gandr"),
            SourceText::from("data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n"),
        );
        scratch.file(
            Path::new("fixture/a-sibling.gandr"),
            SourceText::from(
                "import \"./base.gandr\" ;\ndef one : Nat ;\ndef one = Succ(Zero) ;\ndef two : \
                 Nat ;\ndef two = Succ(one) ;\n",
            ),
        );
        scratch.file(
            Path::new("fixture/b-member.gandr"),
            SourceText::from(
                "import \"./base.gandr\" ;\ndata List(a : Type) : Type {\n  Nil : List(a);\n  \
                 Cons : (head : a, tail : List(a)) --> List(a);\n}\ndef joined : +U (-F \
                 List(Nat)) ;\ndef joined = thunk { return (Cons(Zero, (Nil : List(Nat))) : \
                 List(Nat)) } ;\n",
            ),
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let mut reprinted = Vec::new();
        let ControlFlow::Continue(_) = Walk::new(vec![scratch.root().join("fixture")]).visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path,
                    root,
                    text,
                    base,
                    composed: Composed::Settled { mut program, .. },
                    ..
                } = step
                else {
                    return ControlFlow::Continue(());
                };
                if !path.ends_with("b-member.gandr") {
                    return ControlFlow::Continue(());
                }
                let own =
                    SourceText::from(text.as_ref().get(usize::from(base) ..).unwrap_or_default());
                let Maybe::Present(laid) = lay_out(&grammar, path, root, own)
                else {
                    panic!("the member is laid out beside its import");
                };
                let table = TypeTable::of_unit(
                    &grammar,
                    SourceText::from(laid.text.as_str()),
                    &laid.unit,
                    laid.base,
                )
                .expect("the member's unit parses");
                let Maybe::Present(last) = program.target()
                else {
                    panic!("the component declares");
                };
                let mut named = String::new();
                for position in 0_usize ..= usize::from(last) {
                    let constant = ConstantIndex::from(position);
                    let Maybe::Present(name) = program.name(constant)
                    else {
                        continue;
                    };
                    named.clear();
                    core::fmt::Write::write_fmt(&mut named, format_args!("{name}"))
                        .expect("a name writes");
                    if named != "joined" {
                        continue;
                    }
                    let Evaluation::Value(value) = program.evaluate(constant)
                    else {
                        panic!("`joined` runs to a value");
                    };
                    let presentation = value.presentation();
                    let spelled: &str = presentation.as_ref();
                    let reprint = table.reprint_value(
                        &grammar,
                        Maybe::Present(Name::from("joined")),
                        SourceText::from(spelled),
                    );
                    reprinted.push((String::from(spelled), reprint));
                }
                ControlFlow::Continue(())
            },
        );
        assert_eq!(
            reprinted,
            [(
                String::from("Cons(Zero, Nil)"),
                Maybe::Present(String::from("Cons(Zero, Nil)"))
            )],
            "the member's value reprints under its own declaration's type"
        );
    }

    #[test]
    fn every_kind_of_node_is_typed_where_it_was_written()
    {
        let source =
            SourceText::from("def f(x: Integer) -> -F Integer { return x }\n\ndef g = 1 ;");
        let table = table(source);
        let at = |needle: &'static str| answer(&table, source, SourceText::from(needle));
        assert_eq!(
            at("x }"),
            agreed(Subject::Term, SourceText::from("Integer")),
            "the use is a term of its binder's type"
        );
        assert_eq!(
            at("x:"),
            agreed(Subject::Binder, SourceText::from("Integer")),
            "the binder is spelled at its use's type"
        );
        assert_eq!(
            at("Integer)"),
            agreed(Subject::Type, SourceText::from("Type")),
            "a written type is spelled at its universe"
        );
        assert_eq!(
            at("-F"),
            agreed(Subject::Type, SourceText::from("Type[-]")),
            "a written computation type is spelled at its universe"
        );
        assert!(
            matches!(
                at("return"),
                Maybe::Present(Answer {
                    subject: Subject::Term,
                    ..
                })
            ),
            "the keyword answers the term it opens"
        );
        assert_eq!(
            at("\n\n"),
            Maybe::Absent(typing::Absent::Untyped),
            "layout between declarations is no node's"
        );
    }

    #[test]
    fn a_called_name_runs_and_a_binder_binds()
    {
        let written = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef id : \
                       Nat => Nat ;\ndef id = thunk { fn (y) { pure y } } ;\ndef twice = thunk { fn \
                       (x) { run a <- id(x) ; id(a) } } ;\ndef same(n : Nat) -> -F Nat { n }\n";
        let table = table(SourceText::from(written));
        let names: Vec<String> = table
            .readings()
            .iter()
            .filter_map(|&(span, reading)| {
                let start = usize::from(span.start());
                let text = written.get(start .. usize::from(span.end()))?;
                text.chars()
                    .all(|letter| letter.is_alphanumeric() || letter == '_')
                    .then(|| {
                        let line = written
                            .get(.. start)
                            .unwrap_or_default()
                            .matches('\n')
                            .count()
                            .saturating_add(1);
                        std::format!("{line}:{text} {:?} {:?}", reading.binding, reading.polarity)
                    })
            })
            .collect();
        assert_eq!(
            names,
            [
                "2:Zero Binds Value",
                "3:Succ Binds Value",
                "3:n Binds Value",
                "6:y Binds Value",
                "6:y Uses Value",
                "7:x Binds Value",
                "7:run Uses Computation",
                "7:a Binds Value",
                "7:id Uses Computation",
                "7:x Uses Value",
                "7:id Uses Computation",
                "7:a Uses Value",
                "8:n Binds Value",
                "8:n Uses Value",
            ],
            "a constructor's name, a telescope binder, a lambda binder, a `run` binder and a \
             parameter bind; a called name runs as a computation, the values passed to it are \
             values, and so is the value a body answers, its inferred `return` read as nothing"
        );
    }

    /// #1487: the name of a recursive call, written with its claim as
    /// `plus[<]`, reads as the force that runs the call, as any called name
    /// does.
    #[test]
    fn a_recursive_call_s_name_runs_as_its_force_1487()
    {
        let written = include_str!("../../surface-corpus/fixture/model/data/data-base.gandr");
        let table = table(SourceText::from(written));
        let start = written
            .find("plus[<]")
            .expect("the recursive call is written");
        let name = gandr_surface_syntax::ByteSpan::new(
            gandr_surface_syntax::ByteOffset::from(start),
            gandr_surface_syntax::ByteOffset::from(start.saturating_add(4_usize)),
        )
        .expect("the name is a span");
        let readings = table.readings();
        assert_eq!(
            readings
                .binary_search_by_key(&name, |&(span, _)| span)
                .ok()
                .and_then(|found| readings.get(found))
                .map(|&(_, reading)| reading),
            Some(super::Reading {
                binding: super::Binding::Uses,
                polarity: super::Polarity::Computation,
            }),
            "the recursive call's name is a use run as a computation"
        );
    }

    #[test]
    fn the_binders_in_a_window_answer_alone()
    {
        let source = SourceText::from(
            "def id : Integer => Integer ;\ndef id = thunk { fn (y) { return y } } ;\ndef f(x: \
             Integer) -> -F Integer { return x }\n",
        );
        let table = table(source);
        let line = |number: usize| {
            let start: usize = <&str>::from(source)
                .split_inclusive('\n')
                .take(number)
                .map(str::len)
                .sum();
            let end = start
                + <&str>::from(source)
                    .split_inclusive('\n')
                    .nth(number)
                    .map_or(0, str::len);
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("an ordered span")
        };
        let named = |within: ByteSpan| {
            table
                .binders(within, PageWidth::from(80_u32), Form::Explicit.into())
                .filter_map(|binder| match binder {
                    Maybe::Present(binder) => Some((
                        String::from(
                            <&str>::from(source)
                                .get(
                                    usize::from(binder.span().start())
                                        .. usize::from(binder.span().end()),
                                )
                                .unwrap_or_default(),
                        ),
                        String::from(binder.ty().as_ref()),
                    )),
                    Maybe::Absent(_) => None,
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(named(line(0)), [], "a signature binds nothing");
        assert_eq!(
            named(line(1)),
            [(String::from("y"), String::from("Integer"))],
            "the lambda's binder, at its uses' type"
        );
        assert_eq!(
            named(line(2)),
            [(String::from("x"), String::from("Integer"))],
            "the parameter, and not the lambda's binder beside it"
        );
    }

    #[test]
    fn a_type_under_a_static_binder_answers_as_a_written_type()
    {
        // #404: a type written where a static function takes one is lowered
        // as a code, and answers as every written type does, at its universe
        // or at the operator type ending in one.
        let source = SourceText::from(
            "def pair : Type -> Type[-] ;\ndef pair = \\X. -F (X * X) ;\ndef arrow : Type ;\ndef \
             arrow = +U (Integer -> -F Integer) ;\n",
        );
        let table = table(source);
        let at = |needle: &'static str| answer(&table, source, SourceText::from(needle));
        assert_eq!(
            at("\\X."),
            agreed(Subject::Type, SourceText::from("Type -> Type[-]")),
            "a type family under its static binder"
        );
        assert_eq!(
            at("-F (X"),
            agreed(Subject::Type, SourceText::from("Type[-]")),
            "the computation type it returns"
        );
        assert_eq!(
            at("* X)"),
            agreed(Subject::Type, SourceText::from("Type")),
            "the product under the binder"
        );
        assert_eq!(
            at("+U (Integer"),
            agreed(Subject::Type, SourceText::from("Type")),
            "a thunk type a definition states as a code"
        );
    }

    #[test]
    fn a_printed_type_reads_back_to_its_certificate()
    {
        let source = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef f(x : Nat) -> \
             -F Nat { return x }\ndef h(a : Type, y : a) -> -F a { return y }\ndef k(a : Type, y : \
             a) -> -F a { run z <- h(a, y) ; return z }\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let read = table(source).read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into());
        let trip = |spelled: &str, declared: bool| {
            read.iter()
                .filter(|read| {
                    read.spelled == spelled
                        && matches!(read.site, ReadSite::Declared(_)) == declared
                })
                .map(|read| read.trip.clone())
                .collect::<Vec<RoundTrip>>()
        };
        for (spelled, declared, what) in [
            ("Nat", false, "a data type"),
            ("Type", false, "a universe"),
            ("Type[-]", false, "a computation universe"),
            ("-F Nat", false, "a computation type"),
            (
                "Nat => Nat",
                true,
                "a declaration's thunked function type, sugared",
            ),
        ] {
            let trips = trip(spelled, declared);
            assert!(
                !trips.is_empty() && trips.iter().all(|trip| *trip == RoundTrip::Equal),
                "{what} reads back equal: {trips:?}"
            );
        }
        // `a` under `a`, `y` and `z`: the parameter `y` and the bind's `z`,
        // which the type does not name, read back as binders all the same.
        let open = trip("a", false);
        assert!(
            open.len() >= 2 && open.iter().all(|trip| *trip == RoundTrip::Equal),
            "a term typed under its parameters and a bind reads back equal under them: {open:?}"
        );
    }

    #[test]
    fn a_scoped_capability_answers_at_its_scope()
    {
        let source = SourceText::from(
            "def f() -> -F Unit {\n  handle c : Proc {\n    run d : Cap {exit} at c <- pure c ;\n    \
             c.exit(1)\n  } with {\n    pure(x) => return x,\n    oper exit(code, k) => return \
             unit\n  }\n}\n",
        );
        let table = table(source);
        let used = || answer(&table, source, SourceText::from("c ;"));
        assert!(
            matches!(used(), Maybe::Present(Answer { ref ty, .. }) if ty == "Cap {exit} at c"),
            "a capability in the scope's subject names the scope: {:?}",
            used()
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let read = table.read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into());
        let scoped: Vec<&RoundTrip> = read
            .iter()
            .filter(|read| read.spelled == "Cap {exit} at c")
            .map(|read| &read.trip)
            .collect();
        assert!(
            !scoped.is_empty() && scoped.iter().all(|trip| **trip == RoundTrip::Open),
            "a type naming a scope reads under that scope, as open: {scoped:?}"
        );
    }

    #[test]
    fn a_kept_type_answers_at_the_hold_it_is_kept_in()
    {
        let source = SourceText::from(
            "def f() -> -F Unit {\n  hold s = 3;\n  handle c : Proc {\n    run d : Cap {exit} at \
             c <- pure c ;\n    run k : Integer at s <- pure 1 ;\n    run m <- pure k ;\n    \
             c.exit(1)\n  } with {\n    pure(x) => return x,\n    oper exit(code, k) => return \
             unit\n  }\n}\n",
        );
        let table = table(source);
        let capability = answer(&table, source, SourceText::from("c ;"));
        assert!(
            matches!(capability, Maybe::Present(Answer { ref ty, .. }) if ty == "Cap {exit} at c"),
            "a capability names its scope past the hold around it: {capability:?}"
        );
        let kept = answer(&table, source, SourceText::from("k ;"));
        assert!(
            matches!(kept, Maybe::Present(Answer { ref ty, .. }) if ty == "Integer at s"),
            "a value kept at a hold names the hold: {kept:?}"
        );
    }

    #[test]
    fn a_mismatched_term_shows_both_types()
    {
        let source = SourceText::from("def answer : Integer ; def answer = unit ;");
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("unit")),
            Maybe::Present(Answer {
                subject: Subject::Term,
                ty: String::from("Unit"),
                expected: Maybe::Present(String::from("Integer")),
            }),
            "the term has its own type and the one it was checked against"
        );
    }

    #[test]
    fn a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385()
    {
        let source = SourceText::from(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n\ndata Int : \
             Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  P : (x : Int) --> Int;\n  rule \
             S(P(x)) <=> x;\n  rule P(S(x)) <=> x;\n}\n\ndef tell(p : Path(Circle, Base, Base)) \
             -> -F Integer {\n  case p {\n    here => return 0,\n    loop ∷ q => return 1,\n    \
             back(loop) ∷ q => return 2\n  }\n}\n\ndef rec spin(n : Int) -> -F Path(Circle, \
             Base, Base) {\n  case n {\n    Z => return here(Base),\n    S(x) => { run c <- \
             spin[<](x); return loop ∷ c },\n    P(x) => { run c <- spin[<](x); return \
             back(loop) ∷ c }\n  }\n}\n\ndef flip(x : Circle) -> -F Circle {\n  case x {\n    \
             Base => Base,\n    loop => back(loop)\n  }\n}\n",
        );
        let table = table(source);
        let text = <&str>::from(source);
        // What the table answers at the first byte of `needle`: the bytes the
        // answering entry spans, what it is and its type.
        let at = |needle: &str| {
            let offset = text.find(needle).expect("the needle occurs");
            match table.at(
                ByteOffset::from(offset),
                PageWidth::from(80_u32),
                Form::Sugared.into(),
            ) {
                Maybe::Present(entry) => (
                    String::from(
                        text.get(
                            usize::from(entry.span().start()) .. usize::from(entry.span().end()),
                        )
                        .expect("an entry spans the source"),
                    ),
                    entry.subject(),
                    String::from(entry.ty().as_ref()),
                ),
                Maybe::Absent(reason) => panic!("`{needle}` answers nothing: {reason:?}"),
            }
        };
        let path = "Path(Circle, Base, Base)";
        let pattern =
            |written: &str, ty: &str| (String::from(written), Subject::Binder, String::from(ty));
        assert_eq!(
            at("case p"),
            (
                String::from(
                    "case p {\n    here => return 0,\n    loop ∷ q => return 1,\n    back(loop) ∷ q => return 2\n  }"
                ),
                Subject::Term,
                String::from("?")
            ),
            "the run refused the match's body"
        );
        assert_eq!(
            at("here =>"),
            pattern("here", path),
            "the empty word at the scrutinee's type"
        );
        assert_eq!(
            at("loop ∷ q => return 1"),
            pattern("loop", path),
            "a letter is a word of one letter"
        );
        assert_eq!(
            at("∷ q => return 1"),
            pattern("loop ∷ q", path),
            "the cons at the words' type"
        );
        assert_eq!(
            at("q => return 1"),
            pattern("q", path),
            "the rest at the words' type, though no use of it was judged"
        );
        assert_eq!(
            at("back(loop) ∷ q => return 2"),
            pattern("back", path),
            "the name inverting a letter, a word of one letter"
        );
        assert_eq!(
            at("(loop) ∷ q => return 2"),
            pattern("back(loop) ∷ q", path),
            "the parentheses around the inverted letter answer the cons as a constructor \
             pattern's do (#408)"
        );
        assert_eq!(
            at("loop) ∷ q => return 2"),
            pattern("loop", path),
            "the letter it inverts"
        );
        assert_eq!(
            at("S(x) => {"),
            pattern("S", "Int => Int"),
            "a constructor's name at its type"
        );
        assert_eq!(
            at("(x) => { run c"),
            pattern("S(x)", "Int"),
            "the constructor pattern at its family"
        );
        assert_eq!(
            at("x) => { run c"),
            pattern("x", "Int"),
            "the field at the constructor's field type"
        );
        assert_eq!(
            at("Z => return"),
            pattern("Z", "Int"),
            "a constructor of no field at its family"
        );
        assert_eq!(
            at("loop : Base"),
            pattern("loop", path),
            "a loop's declared name at its path type"
        );
        assert_eq!(
            at("loop => back"),
            pattern("loop", path),
            "a loop arm's loop at its path type"
        );
        assert_eq!(
            at("Base => Base"),
            pattern("Base", "Circle"),
            "the point's arm at the circle"
        );
    }

    #[test]
    fn an_unused_dependent_part_answers_in_its_arms_context()
    {
        let source = SourceText::from(
            "data Vinf : Type[+, 1] {\n  Sup : (a : Type, f : +U (a -> -F Vinf)) --> Vinf;\n}\n\ndef members(v : Vinf) -> -F Type {\n  case v {\n    Sup(a, f) => return a\n  }\n}\n",
        );
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("f) =>")),
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from("+U (a -> -F Vinf)"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "the part names the pattern's own `a`, though the arm never uses it (#537)"
        );
    }

    /// #1439: a capability scope's clause arguments that no body reads answer
    /// at what the scope binds them at: the result at what the subject
    /// returns, the payload at its operation's payload, and the continuation at
    /// the stack from the operation's reply to the scope's answer.
    #[test]
    fn an_unread_clause_argument_answers_at_what_its_scope_binds_1439()
    {
        let source = SourceText::from(
            "def handled() -> -F Unit {\n  handle c : Proc {\n    run code <- c.exit(1) ;\n    \
             pure code\n  } with {\n    pure(x) => pure unit,\n    oper exit(status, k) => pure \
             unit\n  }\n}\n",
        );
        let table = table(source);
        let binder = |ty: &str| {
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from(ty),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            })
        };
        assert_eq!(
            answer(&table, source, SourceText::from("x) =>")),
            binder("Unit"),
            "the result at what the subject returns"
        );
        assert_eq!(
            answer(&table, source, SourceText::from("status, k")),
            binder("Integer"),
            "the payload at `exit`'s"
        );
        assert_eq!(
            answer(&table, source, SourceText::from("k) =>")),
            binder("Stack(-F Unit, -F Unit)"),
            "the continuation from `exit`'s reply to the scope's answer"
        );
    }

    #[test]
    fn a_pattern_on_a_computed_scrutinee_answers_1141()
    {
        let source = SourceText::from(
            "def compared(n : Integer) -> -F Integer {\n  case n >= 5 {\n    true => return \
             2,\n    false => return 1\n  }\n}\n",
        );
        let table = table(source);
        for arm in ["true =>", "false =>"] {
            assert_eq!(
                answer(&table, source, SourceText::from(arm)),
                Maybe::Present(Answer {
                    subject: Subject::Binder,
                    ty: String::from("Bool"),
                    expected: Maybe::Absent(checked_against::Absent::Agreed),
                }),
                "`{arm}` answers at what the comparison it cases on returns, not as the case"
            );
        }
    }

    /// Parts no arm uses answer at their place's type alone: a record
    /// pattern's over a product of three at its own component, and an indexed
    /// sum pattern's over a boolean, the sum of two units it stands for, at
    /// the summand.
    #[test]
    fn a_part_of_a_product_or_a_binary_sum_answers_at_its_component()
    {
        let source = SourceText::from(concat!(
            "def last(t : #{Integer, Bool, Integer}) -> -F Integer {\n",
            "  case t {\n    #{x, y, z} => return z\n  }\n}\n",
            "def side(c : Integer) -> -F Integer {\n  run small <- c < 128;\n",
            "  case small {\n    +{.0 = u} => 1,\n    +{.1 = v} => 2\n  }\n}\n",
        ));
        let table = table(source);
        for (needle, ty) in [("y, z}", "Bool"), ("u} =>", "Unit"), ("v} =>", "Unit")] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "`{needle}` answers at its component"
            );
        }
    }

    /// #1883: a binder no arm reads in a record pattern over a plain record
    /// answers at the field of the label it binds, written out of the type's
    /// order or by position.
    #[test]
    fn an_unread_binder_of_a_plain_record_answers_at_its_field_1883()
    {
        let source = SourceText::from(concat!(
            "def low(r : #{low : Integer, high : Bool}) -> -F Integer {\n",
            "  case r {\n    #{.high = h, .low = l} => return l\n  }\n}\n",
            "def first(r : #{low : Integer, high : Bool}) -> -F Integer {\n",
            "  case r {\n    #{p, q} => return p\n  }\n}\n",
        ));
        let table = table(source);
        for (needle, ty) in [("h, .low", "Bool"), ("q} =>", "Bool")] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "`{needle}` answers at its label's field"
            );
        }
    }

    #[test]
    fn an_unused_part_of_a_static_application_answers_1080()
    {
        let source = SourceText::from(concat!(
            "def twice : Type -> Type ;\ndef twice = \\Y. Y * Y ;\n\n",
            "def twiceFirst(p : twice(Integer)) -> -F Integer {\n",
            "  case p {\n    #{c, d} => return c\n  }\n}\n",
        ));
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("d} =>")),
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from("Integer"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "a part the arm never uses answers at the type the scrutinee's static application \
             reduces to"
        );
    }

    #[test]
    fn a_term_re_formed_under_a_case_answers_at_its_own_type_551()
    {
        let source = SourceText::from(concat!(
            "def made(a : Type, b : Type, i : #{to : +U (a -> -F b), back : +U (b -> -F a), ",
            "sect : (x : a) => Path(a, back(to(x)), x), retr : (y : b) => Path(b, to(back(y)), y)}) ",
            "-> -F #{to : +U (a -> -F b), linv : #{g : +U (b -> -F a), sect : (x : a) => Path(a, g(to(x)), x)}, ",
            "rinv : #{h : +U (b -> -F a), retr : (y : b) => Path(b, to(h(y)), y)}} {\n",
            "  case i {\n    #{t, k, s, r} => #{t, #{#{k, s}, #{k, r}}}\n  }\n}\n",
        ));
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("g(to(x))")),
            Maybe::Present(Answer {
                subject: Subject::Term,
                ty: String::from("+U (b -> -F a)"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "the case's motive judges the result type again under its binders, which is no \
             check of the term in its own context (#551)"
        );
    }

    #[test]
    fn a_pattern_inside_a_dependent_pair_s_second_component_answers_558()
    {
        let source = SourceText::from(concat!(
            "def nested(p : #{x : Integer, inner : #{y : Integer, q : Path(Integer, x, y)}}) ",
            "-> -F Integer {\n  case p {\n    #{x, #{y, q}} => y\n  }\n}\n",
            "def flat(p : #{x : Integer, y : Integer, q : Path(Integer, x, y)}) ",
            "-> -F Integer {\n  case p {\n    #{x, y, q} => y\n  }\n}\n",
        ));
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("#{y, q}")),
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from("#{y : Integer, q : Path(Integer, x, y)}"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "the inner record answers at the pair's second component, under the `x` the \
             outer pattern writes, with the labels it was written with (#558, #1613)"
        );
        assert_eq!(
            answer(&table, source, SourceText::from("#{x, y, q}")),
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from("#{x : Integer, y : #{y : Integer, q : Path(Integer, x, y)}}"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "a record of three answers as itself, not as the pair the lowering nests at its \
             span"
        );
    }

    #[test]
    fn both_halves_of_a_declaration_find_its_type()
    {
        let source = SourceText::from("def answer : Integer ; def answer = 42 ; def other = 7 ;");
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(&grammar, source)
            .expect("the source parses")
            .into_tree();
        let table = table(source);
        let keyed: Vec<String> = tree
            .positions()
            .filter_map(|position| tree.key(position))
            .filter_map(|key| {
                match table.declared(key, PageWidth::from(80_u32), Form::Explicit.into()) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                }
            })
            .collect();
        assert_eq!(
            keyed,
            ["Integer", "Integer", "Integer"],
            "the signature, the definition and the synthesised declaration are each keyed"
        );
    }

    /// A declaration's refusal is read without spelling: it is the refusal
    /// [`TypeTable::declared`] answers, and a typed declaration has none.
    #[test]
    fn a_refusal_is_read_as_the_declaration_answers_it()
    {
        let source = SourceText::from("def answer = 42 ; def sized = 1u32 ;");
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(&grammar, source)
            .expect("the source parses")
            .into_tree();
        let table = table(source);
        let mut read = Vec::new();
        for key in tree.positions().filter_map(|position| tree.key(position)) {
            let declared = table.declared(key, PageWidth::from(80_u32), Form::Explicit.into());
            match (declared, table.refusal(key)) {
                (Maybe::Present(Declared::Refused(held)), Maybe::Present(refusal)) => {
                    assert_eq!(
                        held.as_str(),
                        <&str>::from(refusal),
                        "the refusal is the one held"
                    );
                    read.push("refused");
                },
                (Maybe::Present(Declared::Typed(_)), Maybe::Absent(unrefused::Absent::Typed)) => {
                    read.push("typed");
                },
                (Maybe::Absent(_), Maybe::Absent(unrefused::Absent::Undeclared)) => {},
                (declared, refusal) => {
                    panic!("the two readings disagree: {declared:?} and {refusal:?}")
                },
            }
        }
        assert!(
            read.contains(&"refused") && read.contains(&"typed"),
            "both kinds are read: {read:?}"
        );
    }

    /// A declaration the lowering typed and the checker refused keeps its
    /// type and answers the checker's refusal, as the editor titles it; one
    /// the checker accepted answers none.
    #[test]
    fn a_checker_refusal_is_held_by_its_declaration_1204()
    {
        let source = SourceText::from(
            "data Small : Type {\n  Pick : (a : Type, f : +U (a -> -F Small)) --> Small;\n}\ndata \
             Flag : Type {\n  On : Flag;\n}\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(&grammar, source)
            .expect("the source parses")
            .into_tree();
        let table = table(source);
        let mut read = Vec::new();
        for key in tree.positions().filter_map(|position| tree.key(position)) {
            let declared = table.declared(key, PageWidth::from(80_u32), Form::Explicit.into());
            match (declared, table.refusal(key)) {
                (Maybe::Present(Declared::Typed(ty)), refusal) => {
                    read.push((
                        ty.as_ref().to_owned(),
                        refusal.map(|text| <&str>::from(text).to_owned()),
                    ));
                },
                (Maybe::Absent(_), Maybe::Absent(unrefused::Absent::Undeclared)) => {},
                (declared, refusal) => panic!("unexpected reading: {declared:?} and {refusal:?}"),
            }
        }
        assert_eq!(read.len(), 2, "both declarations are typed: {read:?}");
        assert!(
            read.iter().any(|entry| matches!(
                entry.1,
                Maybe::Present(ref text)
                    if text == "a constructor field exceeds the declared universe"
            )) && read
                .iter()
                .any(|entry| matches!(entry.1, Maybe::Absent(unrefused::Absent::Typed))),
            "the refused declaration answers its refusal and the accepted one none: {read:?}"
        );
    }

    /// A source the lowering refuses as a whole keeps the lowering's message,
    /// where the table holds nothing else; a source of declarations keeps none.
    #[test]
    fn a_source_refused_whole_keeps_its_refusal_1201()
    {
        let refused = table(SourceText::from("nowhere\n"));
        let Maybe::Present(refusal) = refused.refused_whole()
        else {
            panic!("a source refused whole keeps its refusal");
        };
        assert!(
            <&str>::from(refusal).starts_with("the source is not a list of declarations"),
            "the refusal reads as the lowering wrote it: {refusal:?}"
        );
        assert!(
            refused
                .declarations(PageWidth::from(80_u32), Form::Explicit.into())
                .next()
                .is_none(),
            "nothing else is held"
        );
        assert_eq!(
            table(SourceText::from("def answer = 42 ;")).refused_whole(),
            Maybe::Absent(super::wholly::Absent::Lowered),
            "a source of declarations keeps no such refusal"
        );
    }

    /// #298: an offer arm's label answers at the session its endpoint
    /// continues as in that arm — the branch it names of the offer.
    #[test]
    fn an_offer_arm_answers_at_its_branch_298()
    {
        let source = SourceText::from(
            "def exchange(n : Integer) -> -F Unit {\n  fork (c : &{ next : !String. end, retire : \
             end }) {\n    offer(c) {\n      next => { send(c, \"notes\"); close(c) },\n      \
             retire => close(c)\n    }\n  } as peer;\n  select(peer, retire);\n  \
             close(peer)\n}\n",
        );
        let table = table(source);
        for (needle, ty) in [("next =>", "!String. end"), ("retire =>", "end")] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "`{needle}` answers at its branch"
            );
        }
    }

    #[test]
    fn a_sealed_export_is_typed_at_its_atom_by_path()
    {
        let source = SourceText::from(
            "module Counter :> #{ type T, zero : T } { type T = Integer ; def zero = 0 ; }\ndef z = \
             Counter.zero ;",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(&grammar, source)
            .expect("the source parses")
            .into_tree();
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("Counter.zero ;")),
            agreed(Subject::Term, SourceText::from("Counter.T")),
            "a client reads the export at the atom, spelled as it writes it"
        );
        let keyed: Vec<String> = tree
            .positions()
            .filter_map(|position| tree.key(position))
            .filter_map(|key| {
                match table.declared(key, PageWidth::from(80_u32), Form::Explicit.into()) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                }
            })
            .collect();
        assert_eq!(
            keyed,
            ["Counter.T", "Counter.T", "Type", "Counter.T"],
            "every declaration keyed in the source reads the atom by its path, never the \
             representation; the type member reads as the atom, at its kind, as a transparent \
             module's member reads as its witness"
        );
    }

    #[test]
    fn a_theory_member_answers_under_the_sorts_before_it()
    {
        let source = SourceText::from(
            "theory Cat {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  oper id : (a \
             : Ob) --> Hom(a, a);\n  rule idem : id(a) ==> id(a);\n}\n",
        );
        let table = table(source);
        let rows = [
            ("Ob :", Subject::Binder, "Type"),
            ("Hom(dom", Subject::Binder, "+U (Ob -> Ob -> -F Type)"),
            ("dom", Subject::Binder, "Ob"),
            ("id :", Subject::Binder, "+U ((a : Ob) -> -F Hom(a, a))"),
            ("Hom(a, a);", Subject::Type, "Type"),
            ("id(a) ==>", Subject::Term, "+U ((a : Ob) -> -F Hom(a, a))"),
            ("(a) ==>", Subject::Term, "Hom(a, a)"),
        ];
        for (needle, subject, ty) in rows {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(subject, SourceText::from(ty)),
                "{needle}"
            );
        }
    }

    #[test]
    fn a_model_header_answers_no_term_its_signature_derives_477()
    {
        // The members' derived types are located at the theory the header
        // names; their terms once answered there, over binders the naming
        // fallback called after the theory (`CatShape => CatShape`).
        let source = SourceText::from(
            "theory Cat {\n  sort Ob : Type;\n  sort Hom(dom: Ob, cod: Ob) : Type;\n  oper id : (a : \
             Ob) --> Hom(a, a);\n  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  \
             rule unitL : comp(id(a), f) <=> f;\n}\n\nmodule Fns : Model(Cat) {\n  type Ob = \
             Type;\n  type Hom(a : Ob, b : Ob) = +U[ω] (a -> -F b);\n  def ident(t : Type, x : \
             t) -> -F t { return x }\n  def compose(t : Type, u : Type, v : Type, f : +U[ω] (t \
             -> -F u), g : +U[ω] (u -> -F v), x : t) -> -F v {\n    run y <- f(x);\n    become \
             g(y)\n  }\n  def id(t : Type) -> -F (+U[ω] (t -> -F t)) { return thunk { become \
             ident(t) } }\n  def comp(t : Type, u : Type, v : Type, f : +U[ω] (t -> -F u), g : \
             +U[ω] (u -> -F v)) -> -F (+U[ω] (t -> -F v)) {\n    return thunk { become \
             compose(t, u, v, f, g) }\n  }\n  def unitL(p : Type, q : Type, f : +U[ω] (p -> -F \
             q)) -> -F Path((+U[ω] (p -> -F q)), comp(p, p, q, id(p), f), f) {\n    return \
             here(f)\n  }\n}\n",
        );
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("Cat) {")),
            Maybe::Absent(typing::Absent::Untyped)
        );
        assert_eq!(
            answer(&table, source, SourceText::from("id(p), f), f)")),
            agreed(
                Subject::Term,
                SourceText::from("+U ((a : Type) -> -F (+U (a -> -F a)))")
            ),
            "a member the module writes still answers where it is written"
        );
    }

    #[test]
    fn a_data_family_is_keyed_at_its_own_type_past_its_operations()
    {
        let source = SourceText::from(
            "data N : Type {\n  Z : N;\n  S : (n : N) --> N;\n  oper twice(m : N) -> (o : N);\n  \
             rule twice(Z) ==> Z;\n}\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(&grammar, source)
            .expect("the source parses")
            .into_tree();
        let table = table(source);
        let keyed: Vec<String> = tree
            .positions()
            .filter_map(|position| tree.key(position))
            .filter_map(|key| {
                match table.declared(key, PageWidth::from(80_u32), Form::Explicit.into()) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                }
            })
            .collect();
        assert_eq!(
            keyed,
            ["Type"],
            "the family's form, not its operation's type"
        );
        assert_eq!(
            answer(&table, source, SourceText::from("S :")),
            agreed(Subject::Binder, SourceText::from("+U (N -> -F N)")),
            "a constructor at its declared type"
        );
    }

    #[test]
    fn each_label_answers_at_what_it_names()
    {
        let source = SourceText::from(
            "def point : #{n : Integer, s : String} ;\ndef point = #{n = 3, s = \"x\"} ;\ndef \
             tag : +{ok : Integer, err : String} ;\ndef dependent : (a : Type, x : a) => a ;\ndef \
             lazy() -> &{get : -F Integer, put : -F String} { &{.put => return \"s\", .get => \
             return 1} }\n",
        );
        let table = table(source);
        let rows = [
            (
                "n : Integer",
                "Integer",
                "a record type's field at its type",
            ),
            (
                "s = \"x\"",
                "String",
                "a record's field at its value's type",
            ),
            ("err : String", "String", "a sum's summand at its type"),
            (
                "x : a",
                "a",
                "a telescope's binder under the binders before it",
            ),
            (
                "get : -F",
                "-F Integer",
                "a lazy record's observation at its type",
            ),
        ];
        for (needle, ty, reason) in rows {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "{reason}"
            );
        }
    }

    /// #677: a declaration refused for binding again a name an unqualified
    /// import binds answers at none of its sites. Its constructor's name was
    /// answered at the refused family, which prints as the name the import
    /// binds, so the spelling read back as the imported family.
    #[test]
    fn a_declaration_refused_as_shadowing_answers_at_no_site_677()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let sibling = "data Point : Type {\n  Here : Point;\n}";
        let importer = "import \"./point.gandr\" ;\ndata Point : Type {\n  Here : Point;\n}\ndef \
                        here : Point ;\ndef here = Here ;";
        let laid = format!("{sibling}\n{importer}");
        let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        let refused = importer.find("data").zip(importer.find("def"));
        assert!(
            table
                .entries
                .iter()
                .all(|entry| refused.is_some_and(|(start, end)| {
                    usize::from(entry.span.end()) <= start || usize::from(entry.span.start()) >= end
                })),
            "no site of the refused declaration answers: {:?}",
            table.entries
        );
        let at =
            |needle: &str| ByteOffset::from(importer.find(needle).expect("the needle is written"));
        assert!(
            matches!(table.referent(at("Here ;")), Maybe::Present(_)),
            "a name after the refused declaration still refers"
        );
        assert!(
            matches!(table.referent(at("Point;")), Maybe::Absent(_)),
            "a name inside the refused declaration refers to nothing"
        );
        let trips: Vec<(String, RoundTrip)> = table
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        assert!(
            !trips.is_empty() && trips.iter().all(|&(_, ref trip)| *trip == RoundTrip::Equal),
            "the importer's other declarations still read back: {trips:?}"
        );
    }

    /// #298: a `run` binder answers at what its bound computation returns,
    /// whether a use answers it or not: bound to a match with an exit, which
    /// the block's rewrite leaves no bind of, to a loop, unused, or `_`.
    #[test]
    fn a_run_binder_answers_at_what_its_computation_returns_298()
    {
        let source = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\ndef \
             predecessor(n : Nat) -> -F Nat {\n  run m <- case n {\n    Zero => return n,\n    \
             Succ(p) => pure p,\n  } ;\n  return m\n}\n\ndef first(n : Nat) -> -F Nat {\n  run k \
             <- loop { break(Succ(n)) } ;\n  return Succ(k)\n}\n\ndef same(n : Nat) -> -F Nat {\n  \
             return n\n}\n\ndef unused(n : Nat) -> -F Nat {\n  run u <- same(n) ;\n  run _ <- \
             same(n) ;\n  return n\n}\n",
        );
        let table = table(source);
        for (needle, reason) in [
            ("m <-", "bound to a match with an exit"),
            ("k <-", "bound to a loop"),
            ("u <-", "used nowhere"),
            ("_ <-", "discarded"),
        ] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from("Nat")),
                "a binder {reason}"
            );
        }
    }

    /// #298: the patterns of a match a `run` binds answer at the scrutinee's
    /// type, though the block's rewrite copies the match and its scrutinee.
    #[test]
    fn a_run_bound_match_s_patterns_answer_298()
    {
        let source = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\ndef rec skim(n : \
             Nat) -> -F Nat {\n  case n {\n    Zero => return n,\n    Succ(p) => {\n      run _ <- \
             case p {\n        Zero => return p,\n        Succ(r) => pure r,\n      } ;\n      \
             become skim[<](p)\n    },\n  }\n}\n",
        );
        let table = table(source);
        for (needle, ty) in [
            ("Zero => return p", "Nat"),
            ("(r) =>", "Nat"),
            ("r) =>", "Nat"),
        ] {
            assert_eq!(
                answer(&table, source, SourceText::from(needle)),
                agreed(Subject::Binder, SourceText::from(ty)),
                "`{needle}` answers at its place in the scrutinee"
            );
        }
    }

    /// #298: a `run` binder bound to a computation the run judged at a decode
    /// answers at what the decode returns, used or not: `force m` with `m` at
    /// `+U (T(A))`, `T` a static abstraction, returns the abstraction's body at
    /// `A`.
    #[test]
    fn a_run_binder_bound_at_a_decode_answers_at_what_it_returns_298()
    {
        let source = SourceText::from(
            "def raw : (Type -> Type[-]) -> Type -> Type -> Type ;\ndef raw = \\T. \\A. \\B. +U \
             (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;\n\ndef pairs : raw(\\X. -F (X \
             * X), Integer, Integer) ;\ndef pairs = (\n  thunk { fn (a) { return (a, a) } },\n  \
             thunk { fn (m) { fn (k) { run p <- force m ; become (force k)(1) } } }\n) ;\n",
        );
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("p <-")),
            agreed(Subject::Binder, SourceText::from("#{Integer, Integer}")),
            "the unused binder answers at what the decode returns"
        );
    }

    /// #298: a `run`'s tuple pattern answers at the tuple its computation
    /// returns, as a named binder does.
    #[test]
    fn a_run_s_tuple_pattern_answers_at_the_tuple_298()
    {
        let source = SourceText::from(
            "data Nat : Type {\n  Zero : Nat;\n}\n\ndef pair(n : Nat) -> -F (Nat * Nat) {\n  return \
             (n, n)\n}\n\ndef first(n : Nat) -> -F Nat {\n  run (a, b) <- pair(n) ;\n  return \
             a\n}\n",
        );
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("(a, b) <-")),
            agreed(Subject::Binder, SourceText::from("#{Nat, Nat}")),
            "the tuple pattern at what `pair` returns"
        );
    }

    /// A split of a relation whose arm uses only `k` still names `t`, which
    /// the record's later fields mention: the remainder after `t` answers as
    /// two round trips through `k` and `t` (#665).
    #[test]
    fn an_unused_split_component_answers_by_its_written_name_665()
    {
        let spelled = spelled(SourceText::from(
            "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) {\n  case i {\n    #{t, k, s, r} => k\n  }\n}\n",
        ));
        assert!(
            spelled
                .iter()
                .all(|entry| entry.ty().unspelled().is_empty()),
            "no entry spells a `?`: {spelled:#?}"
        );
        assert!(
            spelled.iter().any(|entry| entry.ty().as_ref()
                == "((c : a) => Path(a, k(t(c)), c)) * ((c : b) => Path(b, t(k(c)), c))"),
            "the remainder after `t` names it: {spelled:#?}"
        );
    }

    /// A label pattern leaves the forward map unwritten; the round trips
    /// after it name it by its label, `to`, and where the pattern writes `to`
    /// for another field, by the label primed apart (#670).
    #[test]
    fn an_unwritten_field_answers_by_its_label_670()
    {
        for (pattern, remainder, reason) in [
            (
                "#{.back = k} => k",
                "((c : a) => Path(a, k(to(c)), c)) * ((c : b) => Path(b, to(k(c)), c))",
                "the omitted forward map answers by its label",
            ),
            (
                "#{.back = to} => to",
                "((c : a) => Path(a, to(to′(c)), c)) * ((c : b) => Path(b, to′(to(c)), c))",
                "the label primed apart from the written `to`",
            ),
        ] {
            let source = format!(
                "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) {{\n  case i {{\n    {pattern}\n  }}\n}}\n"
            );
            let spelled = spelled(SourceText::from(source.as_str()));
            assert!(
                spelled
                    .iter()
                    .all(|entry| entry.ty().unspelled().is_empty()),
                "{reason}: no entry spells a `?`: {spelled:#?}"
            );
            assert!(
                spelled.iter().any(|entry| entry.ty().as_ref() == remainder),
                "{reason}: {spelled:#?}"
            );
        }
    }

    /// A dependent record's variables spell under the binders in scope where
    /// each entry stands: at a case under a motive that reads the scrutinee,
    /// where the rest after the first entry answers by the label it starts at,
    /// primed apart from the record's own `y`, and on both sides of an
    /// equivalence as under a function type (#1515).
    #[test]
    fn a_dependent_record_spells_its_variables_where_it_stands_1515()
    {
        let record = "#{ x : b, y : b, p : Path(b, x, y) }";
        let source = format!(
            "def againAt(b : Type, w : {record}) -> -F Path({record}, w, w) {{\n  case w {{\n    \
             #{{.x = u, .y = v, .p = q}} => here((u, (v, q)))\n  }}\n}}\n\ndef selfEquiv(b : \
             Type) -> -F ({record} ≃ {record}) {{\n  (\n    thunk {{ fn (w) {{ w }} }},\n    \
             ((thunk {{ fn (w) {{ w }} }}, thunk {{ fn (w) {{ here(w) }} }}), (thunk {{ fn (w) \
             {{ w }} }}, thunk {{ fn (w) {{ here(w) }} }}))\n  )\n}}\n\ndef selfMap(b : Type) -> \
             -F ({record} => {record}) {{\n  thunk {{ fn (w) {{ w }} }}\n}}\n"
        );
        let source = SourceText::from(source.as_str());
        let spelled = spelled(source);
        assert!(
            spelled
                .iter()
                .all(|entry| entry.ty().unspelled().is_empty()),
            "no entry spells a `?`: {spelled:#?}"
        );
        assert!(
            spelled
                .iter()
                .any(|entry| entry.ty().as_ref().contains("(u, y′)")),
            "the rest of the record answers by its label: {spelled:#?}"
        );
        for (name, declared) in
            table(source).declarations(PageWidth::from(200_u32), Form::Sugared.into())
        {
            let Maybe::Present(super::Declared::Typed(ty)) = declared
            else {
                panic!("`{name:?}` is typed");
            };
            assert!(
                ty.unspelled().is_empty(),
                "`{name:?}`'s declared type spells no `?`: `{ty}` {:?}",
                ty.unspelled()
            );
        }
    }

    /// Every entry of `source`'s table spelled sugared on a page wide enough
    /// that no type wraps.
    ///
    /// # Specification
    /// trivial.
    fn spelled(source: SourceText<'_>) -> Vec<super::TypedSpan>
    {
        table(source)
            .entries(PageWidth::from(200_u32), Form::Sugared.into())
            .filter_map(|entry| match entry {
                Maybe::Present(entry) => Some(entry),
                Maybe::Absent(_) => None,
            })
            .collect()
    }

    /// #675: an equivalence written over function literals checks each law
    /// at its maps put in; every type it prints reads back, the call of a
    /// literal spelled as what it returns rather than as a call the type
    /// grammar cannot read.
    #[test]
    fn a_type_instantiated_at_a_function_literal_reads_back_675()
    {
        let source = SourceText::from(
            "def typeSelf : Type ≃ Type ;\ndef typeSelf = #{thunk { fn (x) { return x } }, \
             #{#{thunk { fn (x) { return x } }, thunk { fn (x) { here(x) } }}, #{thunk { fn (y) \
             { return y } }, thunk { fn (y) { here(y) } }}}} ;\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let trips: Vec<(String, RoundTrip)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        assert!(
            trips
                .iter()
                .any(|&(ref spelled, _)| spelled == "(a : Type) -> -F Path(Type, a, a)"),
            "a law's map spells its call as what it returns: {trips:?}"
        );
        assert!(
            trips.iter().all(|&(_, ref trip)| *trip == RoundTrip::Equal),
            "every printed type reads back: {trips:?}"
        );
    }

    /// #676: a type-valued call nested in a type prints as the nested call
    /// it was written as, never as the run the lowering binds it by, and
    /// reads back; so does each law of an equivalence over such a function.
    #[test]
    fn a_type_valued_call_nested_in_a_type_reads_back_676()
    {
        let source = SourceText::from(
            "def same(x : Type) -> -F Type {\n  return x\n}\n\ndef sameTwice(x : Type) -> -F \
             Path(Type, same(same(x)), x) {\n  return here(x)\n}\n\ndef typeSelf : Type ≃ Type \
             ;\ndef typeSelf = #{same, #{#{same, sameTwice}, #{same, sameTwice}}} ;\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let trips: Vec<(String, RoundTrip)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        for spelled in [
            "(x : Type) -> -F Path(Type, same(same(x)), x)",
            "#{a : Type => Type, b : (b : Type) => Path(Type, same(a(b)), b)}",
        ] {
            assert!(
                trips.iter().any(|&(ref printed, _)| printed == spelled),
                "`{spelled}` is printed: {trips:?}"
            );
        }
        assert!(
            trips.iter().all(|&(_, ref trip)| *trip == RoundTrip::Equal),
            "every printed type reads back: {trips:?}"
        );
    }

    /// #768: a family a record fills with a function literal, applied at a
    /// nested call, prints as what the literal returns and reads back: the
    /// pair of operations into it is the pair of their reducts.
    #[test]
    fn a_family_decoded_at_a_nested_call_reads_back_768()
    {
        let source = SourceText::from(
            "data N : Type {\n  Z : N;\n  S : (n : N) --> N;\n}\n\ndata T : Type {\n  V : T;\n}\n\ndef \
             ext(g : N) -> -F N { return S(g) }\n\ndef k(g : N, t : T) -> -F T { return t }\n\ndef \
             w : #{c : Type, tm : +U (c -> -F Type), e : (g : c) => c, a : (g : c, t : tm(e(g))) \
             => tm(g), b : (g : c, t : tm(e(g))) => tm(g)} ;\ndef w = #{N, #{thunk { fn (g) { \
             return T } }, #{ext, #{k, k}}}} ;\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let trips: Vec<(String, RoundTrip)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        let product: Vec<&RoundTrip> = trips
            .iter()
            .filter(|&&(ref spelled, _)| spelled == "((N, T) => T) * ((N, T) => T)")
            .map(|&(_, ref trip)| trip)
            .collect();
        assert!(
            !product.is_empty() && product.iter().all(|&trip| *trip == RoundTrip::Equal),
            "the pair at the call reads back as what the literal returns: {trips:?}"
        );
    }

    /// #771: a dependent record whose later field names an earlier one only
    /// in a family a literal fills prints, the family read, as the product
    /// it reads as, and reads back as its type.
    #[test]
    fn a_record_whose_dependency_reads_away_reads_back_771()
    {
        let source = SourceText::from(
            "data N : Type {\n  Z : N;\n  S : (n : N) --> N;\n}\n\ndata T : Type {\n  V : T;\n}\n\ndef \
             ext(g : N) -> -F N { return S(g) }\n\ndef k(g : N, t : T) -> -F T { return t }\n\ndef \
             w : #{c : Type, tm : +U (c -> -F Type), e : (g : c) => c, a : (g : c, t : tm(e(g))) \
             => tm(g), b : (g : c, t : tm(e(g))) => tm(g)} ;\ndef w = #{N, #{thunk { fn (g) { \
             return T } }, #{ext, #{k, k}}}} ;\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let trips: Vec<(String, RoundTrip)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect();
        let record: Vec<&RoundTrip> = trips
            .iter()
            .filter(|&&(ref spelled, _)| spelled == "(N => N) * (((N, T) => T) * ((N, T) => T))")
            .map(|&(_, ref trip)| trip)
            .collect();
        assert!(
            !record.is_empty() && record.iter().all(|&trip| *trip == RoundTrip::Equal),
            "the record whose dependency reads away reads back as its type: {trips:?}"
        );
    }

    /// #1655: a dependent record a parameter is typed by, read back under the
    /// parameter before it, reprints with the labels it was written and
    /// printed with: the copy the read-back shifts under that parameter keeps
    /// the labels the reread recorded.
    #[test]
    fn a_record_parameter_reprints_with_its_labels_1655()
    {
        let source = SourceText::from(
            "def againAt(\n  b : Type,\n  w : #{ x : b, y : b, p : Path(b, x, y) }\n) -> -F \
             Path(#{ x : b, y : b, p : Path(b, x, y) }, w, w) {\n  here(w)\n}\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let reads: Vec<(String, Maybe<String, super::reprinted::Absent>)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.reprinted))
            .collect();
        let record = "#{x : b, y : #{y : b, p : Path(b, x, y)}}";
        assert!(
            reads.iter().any(|&(ref spelled, _)| spelled == record),
            "the record prints with its labels: {reads:?}"
        );
        assert!(
            reads.iter().all(|&(ref spelled, ref again)| match *again {
                Maybe::Present(ref again) => again == spelled,
                Maybe::Absent(super::reprinted::Absent::Unspelled) => false,
                Maybe::Absent(
                    super::reprinted::Absent::Unlowered | super::reprinted::Absent::Unrun,
                ) => true,
            }),
            "every printed type that lowers again reprints as itself: {reads:?}"
        );
    }

    /// #1751: a dependent arrow a parameter is typed by, read back under the
    /// parameters before it, two of them dropped from the reread as no later
    /// type names them, reprints with the binder name it was written and
    /// printed with: the copy the read-back shifts under them keeps the name
    /// the reread recorded.
    #[test]
    fn an_arrow_parameter_reprints_with_its_binder_name_1751()
    {
        let source = SourceText::from(
            "def k(\n  a : Type,\n  b : Type,\n  t : a => b,\n  g : b => a,\n  s : (x : a) => \
             Path(a, g(t(x)), x),\n  h : b => a,\n  r : (y : b) => Path(b, t(h(y)), y),\n  y : \
             b\n) -> -F Path((y : b) => Path(b, t(h(y)), y), r, r) { return here(r) }\n",
        );
        let grammar = built_in().expect("the built-in grammar builds");
        let reads: Vec<(String, Maybe<String, super::reprinted::Absent>)> = table(source)
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.reprinted))
            .collect();
        let arrow = "(y : b) => Path(b, t(h(y)), y)";
        assert!(
            reads.iter().any(|&(ref spelled, _)| spelled == arrow),
            "the arrow prints with its written binder: {reads:?}"
        );
        assert!(
            reads.iter().all(|&(ref spelled, ref again)| match *again {
                Maybe::Present(ref again) => again == spelled,
                Maybe::Absent(super::reprinted::Absent::Unspelled) => false,
                Maybe::Absent(
                    super::reprinted::Absent::Unlowered | super::reprinted::Absent::Unrun,
                ) => true,
            }),
            "every printed type that lowers again reprints as itself: {reads:?}"
        );
    }

    /// #776: a document typed after its judged closure — lowered after the
    /// closure's arena, its own declarations typed on the checker's state
    /// after the closure's — answers at every byte, for every declaration,
    /// every declared name and every printed type read back, as the document
    /// typed whole over its unit does. The rose trees import two siblings and
    /// write families, recursion through an imported `map`, cases and a mutual
    /// block.
    #[test]
    fn a_document_typed_after_its_closure_types_as_one_typed_whole_776()
    {
        use alloc::sync::Arc;

        use gandr_surface_corpus::CorpusRoot;
        use gandr_surface_lowering::Unit;
        use gandr_surface_parser::parse;

        use crate::HostGrant;
        use crate::JudgedClosure;
        use crate::LoweringCount;
        use crate::SourceRoot;
        use crate::lay_out;
        use crate::lower_closure;

        let grammar = Arc::new(built_in().expect("the built-in grammar builds"));
        let path = std::fs::canonicalize(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../surface-corpus/fixture/model/data/rose.gandr"),
        )
        .expect("the rose trees are in the corpus");
        let own = std::fs::read_to_string(&path).expect("the rose trees read");
        let Maybe::Present(laid) = lay_out(
            &grammar,
            &path,
            SourceRoot::Fixture,
            SourceText::from(own.as_str()),
        )
        else {
            panic!("the rose trees are laid out after their siblings");
        };
        let sources = laid.unit.sources();
        let closure = Arc::new(
            lower_closure(
                Arc::clone(&grammar),
                String::from(laid.text.get(.. usize::from(laid.base)).unwrap_or_default()),
                Unit::new(
                    sources
                        .get(.. sources.len().saturating_sub(1))
                        .unwrap_or_default()
                        .to_vec(),
                )
                .expect("the siblings make a unit"),
                &mut LoweringCount::default(),
            )
            .expect("the siblings are held"),
        );
        let judged = JudgedClosure::new(
            Arc::clone(&closure),
            &HostGrant::UNBOUNDED,
            CorpusRoot::Fixture,
        )
        .expect("the siblings lower to their end");
        let text = SourceText::from(laid.text.as_str());
        let parsed = parse(&grammar, SourceText::from(own.as_str()))
            .expect("the rose trees parse")
            .after(closure.tree(), text)
            .expect("the rose trees lay after their siblings");
        let after = TypeTable::of_parsed_after(&judged, parsed, &laid.unit, laid.base)
            .expect("the rose trees type after their siblings");
        let whole = TypeTable::of_unit(&grammar, text, &laid.unit, laid.base)
            .expect("the rose trees type whole");
        let page = PageWidth::from(80_u32);
        let differing: Vec<usize> = (0 .. own.len())
            .filter(|&offset| {
                let at = ByteOffset::from(offset);
                after.at(at, page, Form::Explicit.into())
                    != whole.at(at, page, Form::Explicit.into())
            })
            .collect();
        assert!(
            after.spans().nth(100).is_some() && differing.is_empty(),
            "every byte answers alike, over more than a hundred entries: differing at {differing:?}"
        );
        assert!(
            after
                .declarations(page, Form::Explicit.into())
                .eq(whole.declarations(page, Form::Explicit.into())),
            "every declaration answers alike"
        );
        assert_eq!(
            after.declared_names(),
            whole.declared_names(),
            "every declared name is offered alike"
        );
        let read = |table: &TypeTable| -> Vec<(String, RoundTrip)> {
            table
                .read_back(&grammar, page, Form::Sugared.into())
                .into_iter()
                .map(|back| (back.spelled, back.trip))
                .collect()
        };
        assert_eq!(
            read(&after),
            read(&whole),
            "every printed type reads back alike"
        );
    }

    /// A term checked against a type spelled otherwise than its own reads
    /// back at both: its own, and the one it was checked against.
    #[test]
    fn a_mismatched_term_reads_back_at_both_its_types()
    {
        use super::ReadSite;

        let source = SourceText::from("def answer : Integer ; def answer = unit ;");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = table(source);
        let at = <&str>::from(source)
            .find("unit ;")
            .expect("the term is written");
        let sides: Vec<(ReadSite, String)> = table
            .read_back(&grammar, PageWidth::from(80_u32), Form::Explicit.into())
            .into_iter()
            .filter(|back| {
                matches!(back.site, ReadSite::Own(span) | ReadSite::CheckedAgainst(span)
                    if usize::from(span.start()) == at)
            })
            .map(|back| (back.site, back.spelled))
            .collect();
        assert!(
            matches!(sides.as_slice(), [(ReadSite::Own(_), own), (ReadSite::CheckedAgainst(_), against)]
                if against == "Integer" && own != against),
            "the term reads back at its own type, then at the type it was checked against: \
             {sides:?}"
        );
    }

    /// A term checked against a type spelled like its own reads back once, at
    /// its own type. Here the term is the field `b` passed back to `PiL`,
    /// and its two types are distinct nodes printed alike, whose
    /// presentations differ only in the declarations their names link to. A
    /// spelling cannot tell them apart, so a second trip would read the
    /// checked-against type back as the synthesised one.
    #[test]
    fn a_term_checked_against_a_type_spelled_alike_reads_back_once_1791()
    {
        use super::ReadSite;

        let source = SourceText::from(include_str!(
            "../../surface-corpus/fixture/pathological/universe/inductive-recursive.gandr"
        ));
        let grammar = built_in().expect("the built-in grammar builds");
        let table = table(source);
        let at = <&str>::from(source)
            .find("unloop[<](PiL(a, b))")
            .expect("the field is passed back")
            .saturating_add("unloop[<](PiL(a, ".len());
        let sides: Vec<(ReadSite, String)> = table
            .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
            .into_iter()
            .filter(|back| {
                matches!(back.site, ReadSite::Own(span) | ReadSite::CheckedAgainst(span)
                    if usize::from(span.start()) == at)
            })
            .map(|back| (back.site, back.spelled))
            .collect();
        assert!(
            matches!(sides.as_slice(), [(ReadSite::Own(_), own)] if own == "unloop(a) => Loop"),
            "the field reads back once, at its own type: {sides:?}"
        );
    }

    /// Where a code is written as a type, a reader pointing at it means the
    /// type it decodes to, not the code: the decode answers before the code's
    /// own term of the same width.
    #[test]
    fn a_written_code_answers_as_the_type_it_decodes()
    {
        let source = SourceText::from(include_str!(
            "../../surface-corpus/fixture/pathological/universe/closed.gandr"
        ));
        let table = table(source);
        assert!(
            matches!(
                answer(&table, source, SourceText::from("el(c)) -> -F")),
                Maybe::Present(Answer {
                    subject: Subject::Type,
                    ..
                })
            ),
            "the decode of `el(c)` answers, a type"
        );
    }

    /// A name holds the bytes it is written over and not the byte after it:
    /// a declaring name and a use each end where the name does, and the byte
    /// after a use answers what encloses it.
    #[test]
    fn a_name_ends_where_it_is_written()
    {
        let source = SourceText::from(REFERRED);
        let table = table(source);
        let start = |needle: &str| REFERRED.find(needle).expect("the needle is written");
        let declared = start("plus(");
        let used = start("n, p)");
        assert!(
            matches!(
                table.named_at(ByteOffset::from(declared)),
                Maybe::Present(_)
            ),
            "a declaring name holds its first byte"
        );
        assert!(
            matches!(
                table.named_at(ByteOffset::from(declared.saturating_add(4_usize))),
                Maybe::Absent(_)
            ),
            "the byte after a declaring name is not the name's"
        );
        let own = |offset: usize| match table.referent(ByteOffset::from(offset)) {
            Maybe::Present((span, _)) => Some(span),
            Maybe::Absent(_) => None,
        };
        assert_eq!(
            own(used).map(|span| usize::from(span.start())),
            Some(used),
            "a use holds its first byte"
        );
        assert!(
            own(used.saturating_add(1_usize)).is_some_and(|span| usize::from(span.start()) < used),
            "the byte after a use answers the application around it, not the use"
        );
        let pattern = start("Succ(p) =>");
        assert_eq!(
            own(pattern).map(|span| (usize::from(span.start()), usize::from(span.end()))),
            Some((pattern, pattern.saturating_add(4_usize))),
            "a constructor pattern's name refers over its name, not the whole pattern"
        );
    }

    /// A recursive declaration's call refers to the name it calls over the
    /// whole call head, its measure `[<]` included: the declaration binds its
    /// own name, and the head is that binder's written use.
    #[test]
    fn a_recursive_call_s_head_refers_to_the_name_it_calls()
    {
        let text = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec \
                    down(n : Nat) -> -F Nat {\n  case n {\n    Zero => return n,\n    Succ(p) \
                    => become down[<](p)\n  }\n}\n";
        let table = table(SourceText::from(text));
        let declared = text.find("down(").expect("the name is declared");
        let measure = text.find("[<]").expect("the call is written");
        assert_eq!(
            match table.referent(ByteOffset::from(measure)) {
                Maybe::Present((_, referent)) => Some(usize::from(referent.named().start())),
                Maybe::Absent(_) => None,
            },
            Some(declared),
            "the call's measure is part of the head that refers to the name it calls"
        );
    }

    /// #677: a term after a declaration refused for binding again a name an
    /// unqualified import binds still answers; only the refused form's own
    /// sites are set aside.
    #[test]
    fn a_term_after_a_declaration_refused_as_shadowing_still_answers_677()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;

        let sibling = "data Point : Type {\n  Here : Point;\n}";
        let importer =
            "import \"./point.gandr\" ;\ndata Point : Type {\n  Here : Point;\n}\ndef two = 2 ;";
        let laid = format!("{sibling}\n{importer}");
        let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("the unit's sources start in order");
        let grammar = built_in().expect("the built-in grammar builds");
        let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
            .expect("the unit parses");
        let two = importer.find("2 ;").expect("the term is written");
        assert!(
            matches!(
                table.at(
                    ByteOffset::from(two),
                    PageWidth::from(80_u32),
                    Form::Sugared.into()
                ),
                Maybe::Present(_)
            ),
            "the term after the refused declaration answers: {:?}",
            table.entries
        );
    }

    /// #931: a constructor's stated index is read under the family's
    /// parameters and the constructor's fields, and nothing outside it is: a
    /// function written after one stated index and before another answers
    /// under the function's own binders.
    #[test]
    fn only_a_stated_index_answers_under_its_frame_931()
    {
        let source = SourceText::from(
            "data Nat : Type { Z : Nat; S : (n : Nat) --> Nat; }\ndata Vec(a : Type) : Nat -> \
             Type { Nil : Vec(a, Z); Cons : (n : Nat, x : a, xs : Vec(a, n)) --> Vec(a, S(n)); \
             }\ndef g(k : Nat, v : Vec(Nat, k)) -> -F Vec(Nat, k) { return v }\ndata Fin : Nat \
             -> Type { FZ : (m : Nat) --> Fin(S(m)); }\n",
        );
        let table = table(source);
        assert_eq!(
            answer(&table, source, SourceText::from("v }")),
            agreed(Subject::Term, SourceText::from("Vec(Nat, k)")),
            "the use answers under its function's binders"
        );
    }

    /// A rules block's oriented rules each note the direction the order
    /// chose, at the rule's own bytes.
    #[test]
    fn each_oriented_rule_notes_its_direction()
    {
        let text = "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  P : (x : Int) --> \
                    Int;\n  rule S(P(x)) ==> x;\n  rule P(S(x)) ==> x;\n}\n";
        let table = table(SourceText::from(text));
        let noted: Vec<&str> = table
            .orientations()
            .iter()
            .map(|&(span, _)| {
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default()
            })
            .collect();
        assert!(
            noted.len() == 2_usize && noted.iter().all(|rule| rule.contains("==>")),
            "each rule notes its direction at its own bytes: {noted:?}"
        );
    }
}
