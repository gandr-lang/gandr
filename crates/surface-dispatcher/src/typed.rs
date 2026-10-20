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

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Formations;
use gandr_core_checker::Formed;
use gandr_core_checker::HostGrant;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
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
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::TypeImporter;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
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
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::ComponentName;
use gandr_surface_lowering::DeclarationOutcome;
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
use gandr_surface_lowering::SplitComponent;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_lowering::described::DescribedRole;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_pretty::BinderIndex;
use gandr_surface_pretty::ChildSlot;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Scopes;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_computation_line;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::Lowered;
use crate::compose::Lowering;
use crate::compose::LoweringCount;
use crate::compose::adapt;
use crate::compose::judge_lowering;
use crate::compose::lower_parsed_unit;
use crate::compose::lower_unit_source;
use crate::evaluate::Evaluation;
use crate::typed::referent::Referents;

mod referent;

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

/// Where a typed node stands: the declaration whose run first typed it, and
/// the node itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Within
{
    /// The declaration, by the constant it admits.
    constant: ConstantIndex,
    /// The node.
    node: CoreNode,
}

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

/// One intuitionistic binder a typed node stands under: the binder around
/// it, the name the source writes for it, whether it is a capability scope's
/// own, whose region a capability type may name, and the former opening it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Bound
{
    /// The intuitionistic binder around this one.
    around: Option<BinderIndex>,
    /// The name written at the binder, or at a use resolving to it; none
    /// where the source writes none.
    name: Option<String>,
    /// Whether the binder is the capability a scope binds over its subject.
    scope: bool,
    /// The former that opens it, whose type, or whose judgement's, states
    /// the type it binds.
    opener: CoreNode,
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
    /// The capability scopes' names, the first the outermost scope's region.
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

/// The name a split component binds, as the table keeps it: where the
/// pattern variable for it is written, or the label of the field a labelled
/// pattern leaves unwritten.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Named
{
    /// The pattern variable, at its span.
    Written(ByteSpan),
    /// The field's label.
    Labelled(String),
}

/// What the table keeps to name the binders an entry stands under when a
/// reader asks: each declaration's roots, and where the source writes each
/// binder and each use. The scopes are walked one declaration at a time by
/// the answer that needs them, never while the table is built.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Naming
{
    /// The source text the spans index.
    text: String,
    /// Each declaration's declared type and body, ascending by constant.
    roots: Vec<(ConstantIndex, [Option<CoreNode>; 2])>,
    /// Each lambda and bind with where the binder it opens is written,
    /// ascending by id.
    openers: Vec<(ComputationId, ByteSpan)>,
    /// Each split component with the name it binds, ascending by split and
    /// component.
    components: Vec<((ComputationId, SplitComponent), Named)>,
    /// Each dependent arrow with where the name it binds is written,
    /// ascending by id.
    arrows: Vec<(CompTypeId, ByteSpan)>,
    /// Each dependent pair a dependent record's field opens with where the
    /// field's label is written, ascending by id.
    pairs: Vec<(ValueTypeId, ByteSpan)>,
    /// Each type written as a relation between types, with the relation,
    /// ascending by id.
    relations: Vec<(ValueTypeId, Relation)>,
    /// Each written use of a variable with where a name for its binder is
    /// written: first where the origin table records the binder a use
    /// resolves to, then the use itself, which a type's variables have and no
    /// binding records.
    uses: Vec<(ValueId, ByteSpan)>,
}

impl Naming
{
    /// What `module`, lowered from `source`, keeps for naming binders.
    ///
    /// # Specification
    /// - requires: `module` was lowered from `source`.
    /// - ensures: the source text, each value declaration's roots by its
    ///   constant, the origin table's binders, split components, dependent
    ///   arrows, dependent record pairs and relations, and its bindings then
    ///   its written values as uses.
    /// - provides: the input of [`scopes`], kept for an answer.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the record is read only through an answer's
    ///   spelling, which the census witnesses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus census spells every typed node of a body
    ///   under its binders' names, which this record alone supplies; a binder
    ///   or use left out spells `?`, which the census fails on.
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    fn of(
        module: &LoweredModule<'_>,
        source: SourceText<'_>,
    ) -> Self
    {
        let origins = module.origins();
        let mut roots: Vec<(ConstantIndex, [Option<CoreNode>; 2])> = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                let roots = match declaration.outcome() {
                    DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => [
                        Some(CoreNode::ValueType(declared_type)),
                        Some(CoreNode::Value(body)),
                    ],
                    DeclarationOutcome::Uncompleted { declared_type } => {
                        [Some(CoreNode::ValueType(declared_type)), None]
                    },
                    DeclarationOutcome::Bodied { body } => [Some(CoreNode::Value(body)), None],
                    DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World
                    | DeclarationOutcome::Refused(_) => return None,
                };
                Some((declaration.constant(), roots))
            })
            .collect();
        roots.sort_by_key(|&(constant, _)| constant);
        let mut openers: Vec<(ComputationId, ByteSpan)> = origins
            .binders()
            .iter()
            .map(|&(opener, origin)| (opener, origin.span()))
            .collect();
        openers.sort_by_key(|&(opener, _)| opener);
        let components = origins
            .components()
            .iter()
            .map(|&(component, ref name)| {
                (component, match *name {
                    ComponentName::Written(origin) => Named::Written(origin.span()),
                    ComponentName::Labelled(ref label) => {
                        Named::Labelled(String::from(label.as_ref()))
                    },
                })
            })
            .collect();
        let uses = origins
            .bindings()
            .iter()
            .copied()
            .chain(
                origins
                    .values()
                    .iter()
                    .filter(|&&(_, origin)| origin.provenance() == Provenance::Written)
                    .map(|&(variable, origin)| (variable, origin.span())),
            )
            .collect();
        let arrows = origins
            .arrows()
            .iter()
            .map(|&(arrow, origin)| (arrow, origin.span()))
            .collect();
        let pairs = origins
            .pairs()
            .iter()
            .map(|&(pair, origin)| (pair, origin.span()))
            .collect();
        let mut relations = origins.relations().to_vec();
        relations.sort_by_key(|&(related, _)| related);
        Self {
            text: String::from(<&str>::from(source)),
            roots,
            openers,
            components,
            arrows,
            pairs,
            relations,
            uses,
        }
    }

    /// The text the source writes at `span`.
    ///
    /// # Specification
    /// trivial.
    fn written(
        &self,
        span: ByteSpan,
    ) -> Option<String>
    {
        self.text
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .map(String::from)
    }
}

/// What a reprint's own lowering keeps beside the types it read, at their
/// images in the table's arena: the name each dependent arrow binds and the
/// relation each type was written as.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Read
{
    /// Each dependent arrow's image with the name it binds.
    arrows: Vec<(CompTypeId, String)>,
    /// Each related type's image with the relation it was written as.
    relations: Vec<(ValueTypeId, Relation)>,
}

/// What the table keeps for a declaration: its type node, or the lowering's
/// refusal of it as text.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Held
{
    /// The declaration's type node.
    Typed(TypeNode),
    /// The lowering's refusal, as text.
    Refused(String),
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
    /// The binders in scope at each offset of the unit's text the lowering
    /// read under one.
    in_scope: InScope,
}

/// The intuitionistic binder at or around `at`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first intuitionistic binder of the chain from `at` outward;
///   none when the chain holds none.
/// - provides: an entry's context, which skips a fork's linear binders.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// A binder's parent precedes it, so the chain strictly descends.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus census spells each typed node of a body under
///   its binders' names; a chain stopping at a linear binder leaves a `?` the
///   census fails on.
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
#[spec(ensures: |ret| ret.is_none_or(|index| scopes.binder(index).is_some_and(|binder| binder.zone() == Zone::Intuitionistic)))]
fn intuitionistic(
    scopes: &Scopes<CoreNode>,
    at: Option<BinderIndex>,
) -> Option<BinderIndex>
{
    let mut at = at;
    while let Some(index) = at {
        let binder = scopes.binder(index)?;
        if binder.zone() == Zone::Intuitionistic {
            return Some(index);
        }
        at = binder.parent().filter(|&parent| parent < index);
    }
    None
}

/// The binders of one declaration, whose declared type and body are `roots`,
/// each named by what `naming` records for it.
///
/// # Specification
/// - requires: `arena` holds the declaration's nodes and `names` its module's
///   constants'.
/// - ensures: the scopes of every node reachable from `roots`, and for each
///   binder, at its position, the intuitionistic binder around it and its name:
///   the one written for the lambda or bind that opens it, or for the split
///   component it is, counted from the split's outermost binder, or the label
///   of the dependent record field whose pair opens it (#728), else the one
///   written at a use's binder; a split component a label pattern leaves
///   unwritten is named by its field's label, primed (`′`) until no other
///   binder of the declaration holds the name.
/// - provides: the context an entry's type is spelled in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus census spells the types of terms inside
///   bodies, and of endpoints under a signature's binders, by their binders'
///   names; a binder left unnamed spells `?`, which the census fails on. A
///   split component its arm never uses is named all the same, and one a label
///   pattern omits by its label, primed apart from a written name.
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
/// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
/// - witness: `typed::tests::an_unused_split_component_answers_by_its_written_name_665`
/// - witness: `typed::tests::an_unwritten_field_answers_by_its_label_670`
#[spec(ensures: |ret| ret.1.len() == ret.0.binders().len())]
fn scopes(
    arena: &CoreArena,
    names: &[String],
    naming: &Naming,
    roots: [Option<CoreNode>; 2],
) -> (Scopes<CoreNode>, Vec<Bound>)
{
    let names: Vec<Name<'_>> = names.iter().map(|name| Name::from(name.as_str())).collect();
    let printer = CoreSource::new(arena, &names);
    let scopes = Scopes::of(&printer, roots.into_iter().flatten());
    // A split's binders are consecutive, its outermost component first.
    let mut split: Option<(ComputationId, usize)> = None;
    // The binders a label names, primed apart once every binder is named.
    let mut labelled: Vec<usize> = Vec::new();
    let mut bound: Vec<Bound> = scopes
        .binders()
        .enumerate()
        .map(|(at, (_, binder))| {
            let (name, scope) = match binder.opener() {
                CoreNode::Computation(opener) => {
                    let component = match split {
                        Some((held, count)) if held == opener => count.saturating_add(1),
                        Some(_) | None => 0,
                    };
                    split = Some((opener, component));
                    let key = (opener, SplitComponent::from(component));
                    let opened = naming
                        .openers
                        .binary_search_by_key(&opener, |&(held, _)| held)
                        .ok()
                        .and_then(|at| naming.openers.get(at))
                        .and_then(|&(_, span)| naming.written(span));
                    let name = opened.or_else(|| {
                        let held = naming
                            .components
                            .binary_search_by_key(&key, |&(held, _)| held)
                            .ok()
                            .and_then(|at| naming.components.get(at))?;
                        match held.1 {
                            Named::Written(span) => naming.written(span),
                            Named::Labelled(ref label) => {
                                labelled.push(at);
                                Some(label.clone())
                            },
                        }
                    });
                    (
                        name,
                        binder.slot() == ChildSlot::FIRST
                            && matches!(
                                arena.computation(opener),
                                Some(&Computation::Scope { .. })
                            ),
                    )
                },
                CoreNode::ValueType(opener) => {
                    split = None;
                    let labelled = naming
                        .pairs
                        .binary_search_by_key(&opener, |&(held, _)| held)
                        .ok()
                        .and_then(|at| naming.pairs.get(at))
                        .and_then(|&(_, span)| naming.written(span));
                    (labelled, false)
                },
                CoreNode::Value(_) | CoreNode::CompType(_) => {
                    split = None;
                    (None, false)
                },
            };
            Bound {
                around: intuitionistic(&scopes, binder.parent()),
                name,
                scope,
                opener: binder.opener(),
            }
        })
        .collect();
    // A use names the binder it counts out to.
    for &(variable, written_at) in &naming.uses {
        let (Some(Some(innermost)), Some(&Value::Variable { zone, index })) = (
            scopes.innermost(CoreNode::Value(variable)),
            arena.value(variable),
        )
        else {
            continue;
        };
        let Some(name) = naming.written(written_at).filter(|name| {
            !name.is_empty()
                && name
                    .chars()
                    .all(|glyph| glyph.is_alphanumeric() || glyph == '_')
        })
        else {
            continue;
        };
        let chain = scopes.around(Some(innermost), zone);
        if let Some(entry) = usize::try_from(u32::from(index))
            .ok()
            .and_then(|index| chain.get(index))
            .and_then(|&at| bound.get_mut(usize::from(at)))
            && entry.name.is_none()
        {
            entry.name = Some(name);
        }
    }
    // A label is the record's own name for the field, so it stands unless a
    // written name already holds it.
    for at in labelled {
        while bound
            .get(at)
            .and_then(|held| held.name.as_deref())
            .is_some_and(|name| {
                bound
                    .iter()
                    .enumerate()
                    .any(|(other, held)| other != at && held.name.as_deref() == Some(name))
            })
        {
            if let Some(name) = bound.get_mut(at).and_then(|held| held.name.as_mut()) {
                name.push('′');
            }
        }
    }
    (scopes, bound)
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
    ///   which every reading back lowers in again. Unchanged at offset zero
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
        let lowering = lower_parsed_unit(grammar, parsed, unit, &mut LoweringCount::default())?;
        let Lowered::Module { module, mut arena } = lowering.into_lowered()
        else {
            return Ok(Self::default());
        };
        let declarations = adapt(&module);
        let origins = module.origins();
        // Each written type at its universe: the level the typed run formed it
        // at under the binders it was formed under, the first formation kept;
        // a written type no kept formation reached — formed by a rule that
        // forms it outside a formation goal — at the level it reads closed. A
        // transport's written motive is a written type: the family it denotes.
        // So is a decode, the type a code written where a type is read
        // denotes. The run keeps the formations of these types alone.
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
        let written: Vec<(TypeNode, Origin, GroundSort)> = value_types
            .chain(comp_types)
            .chain(motives)
            .filter(|&(_, origin, _)| {
                matches!(
                    origin.provenance(),
                    Provenance::Written | Provenance::Inserted(Insertion::Decode)
                )
            })
            .collect();
        let mut wanted: Vec<TypeNode> = written.iter().map(|&(node, ..)| node).collect();
        wanted.sort_unstable();
        wanted.dedup();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_formations(Formations::Firsts(wanted));
        let typed = type_module(&mut context, &declarations);
        let signatures = context.data_signatures().clone();
        // Each wanted type is formed at most once, so the formations sorted by
        // type find a written type's own by search; the stable sort keeps the
        // first should a type appear twice.
        let mut formed: Vec<&Formed> = typed.values().flat_map(Typings::formed).collect();
        formed.sort_by_key(|formation| formation.ty);
        formed.dedup_by_key(|formation| formation.ty);
        let mut universes = Vec::new();
        for (node, origin, sort) in written {
            let level = match formed.binary_search_by_key(&node, |formation| formation.ty) {
                Ok(at) => match formed.get(at) {
                    Some(formation) => formation.level.clone(),
                    None => continue,
                },
                Err(_) => match level_of(&context, node) {
                    Ok(level) => level,
                    Err(_) => continue,
                },
            };
            universes.push((origin, sort, level));
        }
        let universes: Vec<(Origin, TypeNode)> = universes
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
        let mut kept: Vec<(TermNode, TypeNode, TypeNode, usize, ConstantIndex)> = Vec::new();
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
                    kept.push((term, ty, ty, finished, constant));
                },
            }
        }
        let first_of = |term: TermNode| {
            kept.binary_search_by_key(&term, |&(held, ..)| held)
                .ok()
                .and_then(|at| kept.get(at))
                .map(|&(_, first, _, _, constant)| (first, constant))
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
        let mut order: Vec<&(TermNode, TypeNode, TypeNode, usize, ConstantIndex)> =
            kept.iter().collect();
        order.sort_unstable_by_key(|&&(_, _, _, at, _)| at);
        let mut entries = Vec::with_capacity(order.len());
        for &(term, first, last, _, constant) in order {
            let (origin, node) = match term {
                TermNode::Value(id) => (origins.value(id), CoreNode::Value(id)),
                TermNode::Computation(id) => (origins.computation(id), CoreNode::Computation(id)),
            };
            // A model's derived type is located at the signature its header
            // names, which writes the name and nothing the type holds, so no
            // term in it answers for those bytes (#477); nor does a term of
            // the record a relation between types abbreviates, located at the
            // relation, which writes the two types and nothing the record
            // holds.
            if let Maybe::Present(origin) = origin
                && !matches!(
                    origin.provenance(),
                    Provenance::Inserted(Insertion::Model | Insertion::Relation)
                )
            {
                let (subject, last) = term_subject(&arena, (first, last));
                entries.push(Entry {
                    span: origin.span(),
                    subject,
                    provenance: origin.provenance(),
                    ty: first,
                    last,
                    standing: Standing::Judged(Within { constant, node }),
                });
            }
        }
        let mut binders = BTreeSet::new();
        for &(variable, binder) in origins.bindings() {
            if let Some((first, constant)) = first_of(TermNode::Value(variable))
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
            Some((TypeNode::Value(ty), constant)) => Some(Scrutinised {
                ty,
                within: Within {
                    constant,
                    node: CoreNode::Value(value),
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
        for (span, ty, within, earlier) in
            matched(&module, &mut arena, &scrutinised, &mut constructed)
        {
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
        // What each written computation returns, read at the first judgement
        // the run finished of a computation written there: a `run` binder
        // answers at what its bound computation returns, wherever a rewrite
        // of its block moved that computation (#298), and a computation judged
        // at a decode — `force m` with `m` at `+U (T(A))` — returns what the
        // decode reads as.
        let mut returned: BTreeMap<NodeIndex, (usize, ValueTypeId, Within)> = BTreeMap::new();
        for &(term, first, _, at, constant) in &kept {
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
                    let Some((first, constant)) = first_of(TermNode::Value(value))
                    else {
                        continue;
                    };
                    (
                        first,
                        Standing::Judged(Within {
                            constant,
                            node: CoreNode::Value(value),
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
            let held = match declaration.outcome() {
                DeclarationOutcome::Completed { declared_type, .. }
                | DeclarationOutcome::Uncompleted { declared_type } => {
                    Held::Typed(TypeNode::Value(declared_type))
                },
                DeclarationOutcome::Bodied { body } => match first_type(TermNode::Value(body)) {
                    Some(first) => Held::Typed(first),
                    None => continue,
                },
                DeclarationOutcome::Data(index) => match module.data(index) {
                    Maybe::Present(signature) => Held::Typed(TypeNode::Value(signature.kind())),
                    Maybe::Absent(_) => continue,
                },
                DeclarationOutcome::Abstract(sealing) => Held::Typed(TypeNode::Value(sealing.kind)),
                DeclarationOutcome::World => continue,
                DeclarationOutcome::Refused(refusal) => Held::Refused(refusal.to_string()),
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
        let entries = entries
            .into_iter()
            .filter_map(|entry| {
                Some(Entry {
                    span: own(entry.span, base)?,
                    ..entry
                })
            })
            .collect();
        let referents = Referents::of(&module, &arena, unit, base, &constructed, &hidden);
        Ok(Self {
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
            in_scope: module.into_in_scope(),
        })
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
            .map_or(self.naming.text.len(), |next| usize::from(next.start()));
        self.naming.text.get(start .. end).map(SourceText::from)
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

    /// The written names of the binders in scope at `offset` of the source's
    /// own text, innermost first, a shadowed binder included.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text of each binder [`InScope::binders_at`] answers at
    ///   `offset` moved into the unit's text, in its order.
    /// - provides: the binders a completion at `offset` offers.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the chain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern's binder in its arm and not in its sibling,
    ///   a parameter in the body of a refused declaration.
    /// - witness: `typed::tests::the_binders_in_scope_are_spelled_in_the_source_s_text_831`
    #[inline]
    pub fn binders_at(
        &self,
        offset: ByteOffset,
    ) -> impl Iterator<Item = SourceText<'_>>
    {
        let at = ByteOffset::from(usize::from(offset).saturating_add(usize::from(self.base)));
        self.in_scope.binders_at(at).filter_map(|site| {
            self.naming
                .text
                .get(usize::from(site.start()) .. usize::from(site.end()))
                .map(SourceText::from)
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
    /// - hypothesis: L3 — as [`Self::at`].
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
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
            Maybe::Present(other) if entry.last != entry.ty && other != ty => Maybe::Present(other),
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
    /// - ensures: the refusal the table holds for the declaration, or its type
    ///   spelled; absent as [`typing::Absent::Untyped`] when no declaration has
    ///   the key, and as [`typing::Absent::Unspelled`] when the printer cannot
    ///   lay its type out.
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
            | (Some(&Held::Typed(_)), &(Maybe::Present(Declared::Typed(_)) | Maybe::Absent(typing::Absent::Unspelled))) => true,
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
            Some(&Held::Typed(node)) => match self.spell(node, &Context::default(), page, style) {
                Maybe::Present(spelled) => Maybe::Present(Declared::Typed(spelled)),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            Some(&Held::Refused(ref refusal)) => Maybe::Present(Declared::Refused(refusal.clone())),
            None => Maybe::Absent(typing::Absent::Untyped),
        }
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
            .arrows
            .iter()
            .filter_map(|&(arrow, span)| {
                self.naming
                    .text
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
        let mut relations: Vec<(ValueTypeId, Relation)> = self
            .naming
            .relations
            .iter()
            .chain(&read.relations)
            .copied()
            .collect();
        relations.sort_by_key(|&(related, _)| related);
        let constructors = self.families.naming(&names);
        let printer = CoreSource::new(arena, &names)
            .naming(&constructors)
            .naming_arrows(&arrows)
            .relating(&relations)
            .within(&binders)
            .scoped(&regions);
        present_type(&printer, root(node), page, style)
            .map_or(Maybe::Absent(typing::Absent::Unspelled), Maybe::Present)
    }

    /// The context an entry standing at `standing` is read under: the names
    /// of its intuitionistic binders and of the capability scopes among them,
    /// each outermost first — for a judged node, by walking the scopes of its
    /// declaration alone; for a described member, its context's names and no
    /// scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a judged node, for each intuitionistic binder from the
    ///   outermost to the innermost around the node, the name [`scopes`] gives
    ///   it, and the same name again among the regions for each binder a
    ///   capability scope binds over its subject; for a part standing under the
    ///   parts before it, those of its match's node, then each earlier part's
    ///   name, of no known type; for a described member, each name its context
    ///   binds; empty for a closed node or one its declaration does not reach.
    /// - provides: the context an entry's type is spelled in.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`scopes`], whose witness spells through it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`scopes`]: a body's terms answer under their
    ///   binders' names, and an endpoint under its signature's; a theory's
    ///   operation under the sorts before it; a capability inside a scope's
    ///   subject names the scope.
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_0`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_1`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_2`
    /// - witness: `tests::census::every_typed_entry_spells_without_a_dishonest_question_mark_in_shard_3`
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_scoped_capability_answers_at_its_scope`
    /// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
    fn standing(
        &self,
        standing: Standing,
    ) -> Context
    {
        let (Within { constant, node }, parted) = match standing {
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
        let Some(&(_, roots)) = self
            .naming
            .roots
            .binary_search_by_key(&constant, |&(held, _)| held)
            .ok()
            .and_then(|at| self.naming.roots.get(at))
        else {
            return Context::default();
        };
        let (scopes, mut bound) = scopes(&self.arena, &self.names, &self.naming, roots);
        let mut context = Context::default();
        let mut at = intuitionistic(&scopes, scopes.innermost(node).flatten());
        while let Some(index) = at {
            let Some(binder) = bound.get_mut(usize::from(index))
            else {
                break;
            };
            let name = binder.name.take();
            if binder.scope {
                context.regions.push(name.clone());
            }
            context.binders.push(name);
            context.types.push(self.bound_type(binder.opener));
            at = binder.around.filter(|&around| around < index);
        }
        context.binders.reverse();
        context.regions.reverse();
        context.types.reverse();
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
    ///   lowering refused a closed signature or the whole source.
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
    ///   the type does not name, reads back equal under them; a type of a
    ///   source that imports a sibling reads back beside it; and the corpus
    ///   census reads back every printed type of every source, failing on a
    ///   class the findings do not pin.
    /// - witness: `typed::tests::a_printed_type_reads_back_to_its_certificate`
    /// - witness: `typed::tests::an_importer_s_value_reads_back_beside_its_sibling_552`
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
                if !matches!((&last, &own), (Maybe::Present(last), Maybe::Present(own)) if last == own)
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
            if let Held::Typed(node) = *held {
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
        let mut augmented = self.naming.text.clone();
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
        // A type the lowering recorded as written as a relation stands at each
        // copy a shift made of it, so a type read under a dropped binder
        // reprints as written (#674). The copies are taken in the order the
        // shifts made them, so a copy of a copy finds its source's relation;
        // a type recorded twice keeps its first relation.
        let mut related: BTreeMap<ValueTypeId, Relation> = BTreeMap::new();
        for &(ty, relation) in &read_back.relations {
            related.entry(ty).or_insert(relation);
        }
        for copy in carried {
            let Carried::ValueType(source, image) = copy
            else {
                continue;
            };
            if let Some(&relation) = related.get(&source) {
                read_back.relations.push((image, relation));
                related.entry(image).or_insert(relation);
            }
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
                .and_then(|signed| {
                    self.naming
                        .roots
                        .binary_search_by_key(&signed, |&(held, _)| held)
                        .ok()
                })
                .and_then(|at| self.naming.roots.get(at))
                .and_then(|&(_, [declared, body])| body.and(declared)),
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
        let mut unsigned = self.naming.text.clone();
        unsigned.push_str(&body);
        match self.lowered_reprint(grammar, SourceText::from(unsigned.as_str())) {
            Maybe::Absent(reprinted::Absent::Unlowered) if !signature.is_empty() => {
                let mut signed = self.naming.text.clone();
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
            SourceText::from(self.naming.text.as_str()),
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
///   components at their own; a dependent pair's first at its own and its
///   second at its own, read under the first — and each span the lowering kept
///   for a typed pattern: one read as the pattern at that type, one read as a
///   constructor's name at the constructor's type, which takes the fields to
///   the family as a thunked function and is the family itself for a
///   constructor of no field. A scrutinee the recursion staged is read at the
///   type its stage refines, as the surface writes no stage. A part whose type
///   names a part before it — a data constructor's field, a dependent pair's
///   second — is read under those parts, each written as a binder, and so is
///   every part inside it; a span carries the spans of every binder its type
///   stands under, outermost first. A span under an earlier part not written as
///   a binder answers nothing. A part whose place no rule above types, and
///   every span inside it, answers nothing. Each constructor name read at a
///   data family's type is pushed onto `constructed` with the family's constant
///   and the constructor's tag.
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
///   constructor pattern's name refers to the constructor it names.
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
/// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
/// - witness: `typed::tests::a_pattern_inside_a_dependent_pair_s_second_component_answers_558`
/// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
#[spec(ensures: |ret| ret.iter().all(|&(_, ty, _, _)| arena.value_type(ty).is_some()))]
fn matched(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
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
        while let Some((pattern, ty, under)) = pending.pop() {
            if typed.insert(pattern, (ty, under)).is_some() {
                continue;
            }
            if let Some(shape) = case.patterns.pattern(pattern) {
                pending.extend(
                    parts(arena, &signatures, shape, ty)
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

/// The parts of `pattern`, matched at `ty`, each at the type its place gives
/// it and the number of earlier parts that type stands under.
///
/// # Specification
/// - requires: `ty` is a type of `arena` and `signatures` the module's data
///   families by constant.
/// - ensures: as [`matched`] types the parts of one pattern; none for a pattern
///   whose place it does not type, and none for a leaf. A part stands under no
///   earlier part unless its type names one: a data constructor's field whose
///   type names a field before it stands under every field before it at its
///   declared type, and a dependent pair's second whose type names the first
///   stands under the first.
/// - provides: one step of [`matched`]'s walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match_385`
/// - witness: `typed::tests::an_unused_dependent_part_answers_in_its_arms_context`
/// - witness: `typed::tests::a_pattern_inside_a_dependent_pair_s_second_component_answers_558`
#[spec(ensures: |ret| ret.iter().all(|&(_, part, _)| arena.value_type(part).is_some())
    && (ret.is_empty() || matches!(*pattern, Pattern::Constructor { .. } | Pattern::Pair(..) | Pattern::Injection(..))))]
fn parts(
    arena: &mut CoreArena,
    signatures: &BTreeMap<ConstantIndex, &DataSignature>,
    pattern: &Pattern,
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
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Declared;
    use super::ReadSite;
    use super::RoundTrip;
    use super::Subject;
    use super::TypeTable;
    use super::checked_against;
    use super::typing;

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
            None,
            "the importer's own declaration's name is no use"
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

    /// #831: the binders in scope at an offset of the source's own text are
    /// spelled from that text, the declaration being typed refused.
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
                .map(|name| String::from(<&str>::from(name)))
                .collect::<Vec<_>>()
        };
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
            Width::SERIAL,
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
                ty: String::from("#{a : Integer, b : Path(Integer, x, a)}"),
                expected: Maybe::Absent(checked_against::Absent::Agreed),
            }),
            "the inner record answers at the pair's second component, under the `x` the \
             outer pattern writes (#558)"
        );
        assert_eq!(
            answer(&table, source, SourceText::from("#{x, y, q}")),
            Maybe::Present(Answer {
                subject: Subject::Binder,
                ty: String::from("#{a : Integer, b : #{b : Integer, c : Path(Integer, a, b)}}"),
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
            ["Counter.T", "Counter.T", "Counter.T"],
            "every declaration keyed in the source reads the atom by its path, never the \
             representation; the abstract type itself carries no form key"
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
}
