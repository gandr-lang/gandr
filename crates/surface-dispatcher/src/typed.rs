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
//!   family's.
//! - **A described member** — a `sign` block's sorts, operations, laws and
//!   circuits, a `data` family's constructors, operations and rules, each port
//!   and each node of a rule's sides — is spelled at the type its member states
//!   ([`LoweredModule::described_types`]): the typed run judges none of them,
//!   since the description route reads them. A sign's member is read under the
//!   members before it, named as the sign writes them.
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
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::Typings;
use gandr_core_checker::level_of;
use gandr_core_checker::type_module;
use gandr_core_term::Binders;
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
use gandr_core_term::equal_type_reading;
use gandr_core_term::instantiate_value_type;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::shift_value;
use gandr_core_term::shift_value_type_under;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::Insertion;
use gandr_surface_lowering::Labelled;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::PatternReading;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::described::DescribedRole;
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
use crate::compose::compose;
use crate::compose::lower_source;
use crate::evaluate::Evaluation;

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
}

/// A context the lowering names, by its place in [`TypeTable::contexts`].
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamedContext(usize);

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
    /// Each dependent arrow with where the name it binds is written,
    /// ascending by id.
    arrows: Vec<(CompTypeId, ByteSpan)>,
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
    ///   constant, the origin table's binders and dependent arrows, and its
    ///   bindings then its written values as uses.
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
    /// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
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
        Self {
            text: String::from(<&str>::from(source)),
            roots,
            openers,
            arrows,
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
/// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
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
///   the one written for the lambda or bind that opens it, else the one written
///   at a use's binder.
/// - provides: the context an entry's type is spelled in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus census spells the types of terms inside
///   bodies, and of endpoints under a signature's binders, by their binders'
///   names; a binder left unnamed spells `?`, which the census fails on.
/// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
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
    let mut bound: Vec<Bound> = scopes
        .binders()
        .map(|(_, binder)| {
            let (name, scope) = match binder.opener() {
                CoreNode::Computation(opener) => (
                    naming
                        .openers
                        .binary_search_by_key(&opener, |&(held, _)| held)
                        .ok()
                        .and_then(|at| naming.openers.get(at))
                        .and_then(|&(_, span)| naming.written(span)),
                    binder.slot() == ChildSlot::FIRST
                        && matches!(arena.computation(opener), Some(&Computation::Scope { .. })),
                ),
                CoreNode::Value(_) | CoreNode::ValueType(_) | CoreNode::CompType(_) => {
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
    ///   static Π ending in one — that no check against another type moved;
    ///   each binder the origin table records for a typed use is one entry at
    ///   the binder's span, at that use's type; each written value or
    ///   computation type whose level the checker reads is an entry at its
    ///   universe; each declaration is keyed by each form key it carries, at
    ///   its declared type, its body's synthesised type, its data universe, or
    ///   a sealed abstract type's kind, or holding the lowering's refusal of it
    ///   as text, a `data` family's operations leaving the family's key its
    ///   own; each node a `sign` block or a `data` family's constructors,
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
    ///   declaration entries and the expected type; a sign's members and a data
    ///   family with an operation answer at their own types; a type written
    ///   where a static function takes one answers as a written type.
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_type_under_a_static_binder_answers_as_a_written_type`
    /// - witness: `typed::tests::a_mismatched_term_shows_both_types`
    /// - witness: `typed::tests::both_halves_of_a_declaration_find_its_type`
    /// - witness: `typed::tests::a_sign_member_answers_under_the_sorts_before_it`
    /// - witness: `typed::tests::a_data_family_is_keyed_at_its_own_type_past_its_operations`
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
        let lowering = lower_source(grammar, source, &mut LoweringCount::default())?;
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
        // off its ends.
        let mut judged: Vec<(TermNode, usize, TypeNode, ConstantIndex)> = typed
            .iter()
            .flat_map(|(&constant, typings)| {
                typings
                    .typings()
                    .iter()
                    .map(move |typing| (constant, typing))
            })
            .enumerate()
            .map(|(finished, (constant, typing))| (typing.term, finished, typing.ty, constant))
            .collect();
        judged.sort_unstable_by_key(|&(term, finished, ..)| (term, finished));
        let mut kept: Vec<(TermNode, TypeNode, TypeNode, usize, ConstantIndex)> = Vec::new();
        for (term, finished, ty, constant) in judged {
            match kept.last_mut() {
                Some(&mut (held, _, ref mut last, ref mut at, _)) if held == term => {
                    *last = ty;
                    *at = finished;
                },
                Some(_) | None => kept.push((term, ty, ty, finished, constant)),
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
            if let Maybe::Present(origin) = origin {
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
        for (span, ty, within) in matched(&module, &mut arena, &scrutinised) {
            if binders.insert(span) {
                entries.push(Entry {
                    span,
                    subject: Subject::Binder,
                    provenance: Provenance::Written,
                    ty: TypeNode::Value(ty),
                    last: TypeNode::Value(ty),
                    standing: Standing::Judged(within),
                });
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
                DeclarationOutcome::Refused(refusal) => Held::Refused(refusal.to_string()),
            };
            for key in [
                declaration.signature(),
                declaration.definition(),
                declaration.duplicate(),
            ] {
                if let Maybe::Present(key) = key {
                    let _replaced = declared.insert(key, held.clone());
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
                orientations.push((span, note));
            }
        }
        Ok(Self {
            entries,
            declared,
            arena,
            names,
            naming: Naming::of(&module, source),
            families: Families::of(&module),
            contexts,
            orientations,
            signatures,
            opened,
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

    /// The innermost typed node whose span holds `offset`, spelled in `form`
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
        form: Form,
    ) -> Maybe<TypedSpan, typing::Absent>
    {
        self.chosen(offset)
            .map_or(Maybe::Absent(typing::Absent::Untyped), |entry| {
                self.answer(entry, page, form)
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
    /// - witness: `entries::entries::every_judged_node_answers_at_its_own_span`
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
    /// each spelled in `form` on a page of `page` columns as [`Self::at`]
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
        form: Form,
    ) -> impl Iterator<Item = Maybe<TypedSpan, typing::Absent>> + '_
    {
        self.entries
            .iter()
            .map(move |entry| self.answer(entry, page, form))
    }

    /// `entry` spelled in `form` on a page of `page` columns.
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
        form: Form,
    ) -> Maybe<TypedSpan, typing::Absent>
    {
        let binders = self.standing(entry.standing);
        let Maybe::Present(ty) = self.spell(entry.ty, &binders, page, form)
        else {
            return Maybe::Absent(typing::Absent::Unspelled);
        };
        let expected = match self.spell(entry.last, &binders, page, form) {
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
    /// `key`, a type spelled in `form` on a page of `page` columns.
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
        form: Form,
    ) -> Maybe<Declared, typing::Absent>
    {
        match self.declared.get(&key) {
            Some(&Held::Typed(node)) => match self.spell(node, &Context::default(), page, form) {
                Maybe::Present(spelled) => Maybe::Present(Declared::Typed(spelled)),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            Some(&Held::Refused(ref refusal)) => Maybe::Present(Declared::Refused(refusal.clone())),
            None => Maybe::Absent(typing::Absent::Untyped),
        }
    }

    /// Every declaration's form key with its type or refusal, a type spelled
    /// in `form` on a page of `page` columns, in key order.
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
        form: Form,
    ) -> impl Iterator<Item = (NodeKey, Maybe<Declared, typing::Absent>)> + '_
    {
        self.declared
            .keys()
            .map(move |&key| (key, self.declared(key, page, form)))
    }

    /// `node` spelled through the shared printer in `form` on a page of `page`
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
        form: Form,
    ) -> Maybe<Presentation, typing::Absent>
    {
        self.spell_in(&self.arena, node, context, &[], page, form)
    }

    /// `node` of `arena` spelled as [`Self::spell`] spells a node of the
    /// table's own arena: `arena` holds the table's nodes at their ids, so the
    /// constants and constructors are named alike, and each dependent arrow
    /// `read` names past them binds the name it holds.
    ///
    /// # Specification
    /// trivial.
    fn spell_in(
        &self,
        arena: &CoreArena,
        node: TypeNode,
        context: &Context,
        read: &[(CompTypeId, String)],
        page: PageWidth,
        form: Form,
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
                read.iter()
                    .map(|&(arrow, ref name)| (arrow, Name::from(name.as_str()))),
            )
            .collect();
        arrows.sort_by_key(|&(arrow, _)| arrow);
        let constructors = self.families.naming(&names);
        let printer = CoreSource::new(arena, &names)
            .naming(&constructors)
            .naming_arrows(&arrows)
            .within(&binders)
            .scoped(&regions);
        present_type(&printer, root(node), page, form)
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
    ///   capability scope binds over its subject; for a described member, each
    ///   name its context binds; empty for a closed node or one its declaration
    ///   does not reach.
    /// - provides: the context an entry's type is spelled in.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`scopes`], whose witness spells through it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`scopes`]: a body's terms answer under their
    ///   binders' names, and an endpoint under its signature's; a sign's
    ///   operation under the sorts before it; a capability inside a scope's
    ///   subject names the scope.
    /// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
    /// - witness: `typed::tests::every_kind_of_node_is_typed_where_it_was_written`
    /// - witness: `typed::tests::a_sign_member_answers_under_the_sorts_before_it`
    /// - witness: `typed::tests::a_scoped_capability_answers_at_its_scope`
    fn standing(
        &self,
        standing: Standing,
    ) -> Context
    {
        let Within { constant, node } = match standing {
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
            Standing::Judged(within) => within,
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
    ///   `name : type, ` with its type spelled in `form` on a page of `page`
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
        form: Form,
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
            let Maybe::Present(spelled) = self.spell(TypeNode::Value(ty), &before, page, form)
            else {
                return None;
            };
            if !spelled.unspelled().is_empty() {
                return None;
            }
            let name = name
                .clone()
                .unwrap_or_else(|| format!("read_back_bound_{at}"));
            for part in [name.as_str(), " : ", spelled.to_string().as_str(), ", "] {
                parameters.push_str(part);
            }
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
    /// `form` on a page of `page` columns and read back: parsed as a
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
    ///   whole lowered once, and is [`RoundTrip::Equal`] when the type read is
    ///   the table's node, `U C` for a computation type, compared by
    ///   [`equal_type_reading`] under the source's data signatures — the same
    ///   syntax with path evidence erased, a type of words as the path at its
    ///   point, a session type by its protocol's behaviour from its state;
    ///   [`RoundTrip::Different`] otherwise; and [`RoundTrip::Refused`] with
    ///   the refusal when the lowering refused a closed signature or the whole
    ///   source.
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
    ///   the type does not name, reads back equal under them; and the corpus
    ///   census reads back every printed type of every source, failing on a
    ///   class the findings do not pin.
    /// - witness: `typed::tests::a_printed_type_reads_back_to_its_certificate`
    /// - witness: `census::census::sweeps::every_printed_type_reads_back_to_its_certificate`
    #[spec(ensures: |ret| ret.len() >= self.entries.len())]
    #[inline]
    #[must_use]
    pub fn read_back(
        &self,
        grammar: &Pbg,
        page: PageWidth,
        form: Form,
    ) -> Vec<ReadBack>
    {
        // Each printed type with the node it was printed from, its trip when
        // it is settled before any lowering, and for a type naming a binder
        // the binders it stands under with the parameters declaring them.
        let mut printed: Vec<Printed> = Vec::new();
        for entry in &self.entries {
            let binders = self.standing(entry.standing);
            let own = self.spell(entry.ty, &binders, page, form);
            let mut sides = Vec::from([(ReadSite::Own(entry.span), entry.ty, own.clone())]);
            if entry.last != entry.ty {
                let last = self.spell(entry.last, &binders, page, form);
                if !matches!((&last, &own), (Maybe::Present(last), Maybe::Present(own)) if last == own)
                {
                    sides.push((ReadSite::CheckedAgainst(entry.span), entry.last, last));
                }
            }
            for (site, node, spelled) in sides {
                printed.push(match spelled {
                    Maybe::Present(spelled) => {
                        let closed = self.spell(node, &Context::default(), page, form);
                        let (settled, under) = if !spelled.unspelled().is_empty() {
                            (Some(RoundTrip::Unknown), None)
                        }
                        else if matches!(closed, Maybe::Present(ref closed) if *closed == spelled)
                        {
                            (None, None)
                        }
                        else {
                            self.telescope(&binders, page, form)
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
                printed.push(match self.spell(node, &Context::default(), page, form) {
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
            let whole = format!("def read_back{written}");
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
        // arrows, at the arrows' images, so a reprint binds what was written.
        let mut read_arrows: Vec<(CompTypeId, String)> = Vec::new();
        match lower_source(
            grammar,
            SourceText::from(augmented.as_str()),
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
                        | DeclarationOutcome::Abstract(_)) => Err(format!("{other:?}")),
                    };
                    let _first = lowered.insert(String::from(name.as_ref()), outcome);
                }
                for &(arrow, origin) in module.origins().arrows() {
                    let span = origin.span();
                    if let (Some(image), Some(name)) = (
                        importer.comp_type_image(arrow),
                        augmented.get(usize::from(span.start()) .. usize::from(span.end())),
                    ) {
                        read_arrows.push((image, String::from(name)));
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
        let last_parameter =
            |arena: &mut CoreArena, declared: ValueTypeId, count: usize| -> Option<ValueTypeId> {
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
                            ty = shift_value_type_under(arena, ty, scope, Binders::ONE);
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
        for (name, &count) in &parameterised {
            let Some(read) = lowered.get_mut(name)
            else {
                continue;
            };
            let Ok(declared) = *read
            else {
                continue;
            };
            *read = last_parameter(&mut arena, declared, count)
                .ok_or_else(|| String::from("the declaration is no function of its parameters"));
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
                            match self.spell_in(&arena, again, &context, &read_arrows, page, form) {
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
    /// from as the value a run of `signed` returns and printed again as a run
    /// prints it: the printer's fixed point over the values it prints,
    /// `print(parse(print(v)))`.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the table was built under.
    /// - ensures: `written` appended to the source as the body of a fresh thunk
    ///   declaration, read first as it is written, with no signature: the whole
    ///   lowered once and the thunk's computation printed as a run's value
    ///   prints, on one line in the sugared form, its constants and
    ///   constructors named as the table names them. Where that reading is
    ///   refused — a constructor needs the type its position states — and
    ///   `signed` declares a type, the declaration is signed with it, with the
    ///   computation returning it when it is no thunk, the whole source judged
    ///   and the fresh declaration run, its value spelled as the run spells it;
    ///   [`reprinted::Absent::Unrun`] when the source did not settle or the run
    ///   reached no value. [`reprinted::Absent::Unlowered`] when the lowering
    ///   refused it or the source, and [`reprinted::Absent::Unspelled`] when
    ///   the printer could not lay it out.
    /// - provides: the reprint a presentation census compares a printed value
    ///   with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the census reprints every run value and normal form
    ///   the corpus states; a value whose spelling lowers to another prints
    ///   otherwise and fails it.
    /// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
    #[inline]
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    pub fn reprint_value(
        &self,
        grammar: &Pbg,
        signed: Maybe<ConstantIndex, signed::Absent>,
        written: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        const NAME: &str = REPRINTED;
        let declared = match signed {
            Maybe::Present(signed) => self
                .naming
                .roots
                .binary_search_by_key(&signed, |&(held, _)| held)
                .ok()
                .and_then(|at| self.naming.roots.get(at))
                .and_then(|&(_, [declared, body])| body.and(declared)),
            Maybe::Absent(signed::Absent::Unsigned) => None,
        };
        let signature = if let Some(CoreNode::ValueType(declared)) = declared {
            let Maybe::Present(spelled) = self.spell(
                TypeNode::Value(declared),
                &Context::default(),
                PageWidth::from(u32::from(u16::MAX)),
                Form::Sugared,
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
                Self::run_reprinted(grammar, SourceText::from(signed.as_str()))
            },
            again @ (Maybe::Present(_) | Maybe::Absent(_)) => again,
        }
    }

    /// The thunk the declaration [`REPRINTED`] of `source` defines, lowered
    /// and its computation printed as a run's value prints.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the source is read under.
    /// - ensures: the computation on one line in the sugared form, its
    ///   constants and constructors named as the table names them;
    ///   [`reprinted::Absent::Unlowered`] when the lowering refused the source
    ///   or the declaration, or defined no thunk, and
    ///   [`reprinted::Absent::Unspelled`] when the printer could not lay it
    ///   out.
    /// - provides: the unsigned half of [`Self::reprint_value`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reprint_value`].
    /// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    fn lowered_reprint(
        &self,
        grammar: &Pbg,
        source: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        let Ok(Lowered::Module { module, arena }) =
            lower_source(grammar, source, &mut LoweringCount::default())
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
        let constructors = self.families.naming(&names);
        let printer = CoreSource::new(&arena, &names).naming(&constructors);
        present_computation_line(&printer, CoreNode::Computation(computation), Form::Sugared)
            .map_or(Maybe::Absent(reprinted::Absent::Unspelled), |again| {
                Maybe::Present(again.to_string())
            })
    }

    /// The value the declaration [`REPRINTED`] of `source` runs to, spelled as
    /// a run spells it.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the source is read under.
    /// - ensures: the run's spelling when the source settles as a whole and the
    ///   declaration runs to a value; [`reprinted::Absent::Unlowered`] when the
    ///   source is refused or faults, [`reprinted::Absent::Unrun`] when no
    ///   declaration is [`REPRINTED`] or its run reaches no value.
    /// - provides: the run half of [`Self::reprint_value`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reprint_value`].
    /// - witness: `census::census::every_typed_entry_spells_without_a_dishonest_question_mark`
    #[spec(ensures: |ref ret| !matches!(*ret, Maybe::Present(ref again) if again.is_empty()))]
    fn run_reprinted(
        grammar: &Pbg,
        source: SourceText<'_>,
    ) -> Maybe<String, reprinted::Absent>
    {
        let Ok(Composed::Settled { mut program, .. }) = compose(
            grammar,
            CorpusRoot::Fixture,
            source,
            &mut LoweringCount::default(),
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
                Evaluation::Blamed(_)
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
/// typed, each at what it answers, and where it stands.
///
/// # Specification
/// - requires: `arena` is the one `module` was lowered into and `scrutinised`
///   holds the first kept type of each match's scrutinee, keyed by the
///   scrutinee's syntax node.
/// - ensures: for each match whose scrutinee is in `scrutinised` at a type
///   other than the unknown one, each root pattern at the scrutinee's type and
///   each part at the type its place gives it — a data constructor's field at
///   the field's type, its parameters read at the family's arguments; a word
///   pattern's rest at the word's type; a product's, a pair's, a dependent
///   pair's first and a sum's components at their own — and each span the
///   lowering kept for a typed pattern: one read as the pattern at that type,
///   one read as a constructor's name at the constructor's type, which takes
///   the fields to the family as a thunked function and is the family itself
///   for a constructor of no field. A scrutinee the recursion staged is read at
///   the type its stage refines, as the surface writes no stage. A part whose
///   place no rule above types, and every span inside it, answers nothing.
/// - provides: the pattern half of [`TypeTable::of`].
/// - fails: never; an untyped pattern answers nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a word pattern's empty word, letter, cons and rest, a
///   data constructor pattern's name and field, in a declaration the run
///   settled and in one it refused, and a constructor pattern on a staged
///   scrutinee, are asserted at their types.
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match`
#[spec(ensures: |ret| ret.iter().all(|&(_, ty, _)| arena.value_type(ty).is_some()))]
fn matched(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
    scrutinised: &BTreeMap<NodeIndex, Scrutinised>,
) -> Vec<(ByteSpan, ValueTypeId, Within)>
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
    let mut typed: BTreeMap<PatternId, ValueTypeId> = BTreeMap::new();
    let mut pending: Vec<(PatternId, ValueTypeId)> = Vec::new();
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
        pending.extend(case.arms.iter().map(|arm| (arm.pattern, ty)));
        while let Some((pattern, ty)) = pending.pop() {
            if typed.insert(pattern, ty).is_some() {
                continue;
            }
            if let Some(shape) = case.patterns.pattern(pattern) {
                pending.extend(parts(arena, &signatures, shape, ty));
            }
        }
        for written in &case.spans {
            let Some(&ty) = typed.get(&written.pattern)
            else {
                continue;
            };
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
            matched.push((written.span, answered, within));
        }
    }
    matched
}

/// The parts of `pattern`, matched at `ty`, each at the type its place gives
/// it.
///
/// # Specification
/// - requires: `ty` is a type of `arena` and `signatures` the module's data
///   families by constant.
/// - ensures: as [`matched`] types the parts of one pattern; none for a pattern
///   whose place it does not type, and none for a leaf.
/// - provides: one step of [`matched`]'s walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match`
#[spec(ensures: |ret| ret.iter().all(|&(_, part)| arena.value_type(part).is_some())
    && (ret.is_empty() || matches!(*pattern, Pattern::Constructor { .. } | Pattern::Pair(..) | Pattern::Injection(..))))]
fn parts(
    arena: &mut CoreArena,
    signatures: &BTreeMap<ConstantIndex, &DataSignature>,
    pattern: &Pattern,
    ty: ValueTypeId,
) -> Vec<(PatternId, ValueTypeId)>
{
    let at = |components: &[ValueTypeId], parts: &[PatternId]| -> Vec<(PatternId, ValueTypeId)> {
        if components.len() == parts.len() {
            parts
                .iter()
                .copied()
                .zip(components.iter().copied())
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
                    return fields.iter().map(|&field| (field, ty)).collect();
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
                Maybe::Present(declared) => at(&declared, fields),
                Maybe::Absent(named::Absent::Undeclared) => Vec::new(),
            }
        },
        Pattern::Pair(first, second) => match arena.value_type(ty) {
            Some(&ValueType::Product(ref components)) => at(components, &[first, second]),
            Some(&ValueType::Sigma {
                first: component, ..
            }) => Vec::from([(first, component)]),
            Some(_) | None => Vec::new(),
        },
        Pattern::Injection(side, body) => match arena.value_type(ty) {
            Some(&ValueType::Sum(ref summands)) if summands.len() == 2_usize => {
                let summand = match side {
                    Side::Left => summands.first(),
                    Side::Right => summands.get(1_usize),
                };
                summand
                    .map(|&summand| (body, summand))
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
///   family's arguments substituted for its parameters, outermost first, as the
///   checker's branch types read them.
/// - provides: what a data constructor pattern's parts and name are typed by.
/// - fails: never; a family the module does not declare, an argument count
///   other than its parameters', or a tag past its constructors answers
///   [`named::Absent::Undeclared`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match`
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
    for &field in fields {
        let mut subject = field;
        for (index, &argument) in arguments.iter().enumerate().rev() {
            let depth = Binders::from(u32::try_from(index).unwrap_or(u32::MAX));
            let argument = shift_value(arena, argument, depth);
            subject = instantiate_value_type(arena, subject, argument);
        }
        declared.push(subject);
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
///   its fields' types, as a data declaration's constructor is described.
/// - provides: what the name of a constructor pattern answers at.
/// - fails: never; any other pattern, or one at a type no data family
///   classifies, answers [`named::Absent::Undeclared`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched`].
/// - witness: `typed::tests::a_pattern_answers_as_itself_in_a_settled_and_a_refused_match`
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
    let mut chain = arena.comp_type_returner(ty);
    for &field in fields.iter().rev() {
        chain = arena.comp_type_arrow(field, chain);
    }
    Maybe::Present(arena.value_type_thunk(chain))
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
            Form::Explicit,
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
        let read = table(source).read_back(&grammar, PageWidth::from(80_u32), Form::Sugared);
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
        let read = table.read_back(&grammar, PageWidth::from(80_u32), Form::Sugared);
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
    fn a_pattern_answers_as_itself_in_a_settled_and_a_refused_match()
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
                Form::Sugared,
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
            .filter_map(
                |key| match table.declared(key, PageWidth::from(80_u32), Form::Explicit) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                },
            )
            .collect();
        assert_eq!(
            keyed,
            ["Integer", "Integer", "Integer"],
            "the signature, the definition and the synthesised declaration are each keyed"
        );
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
            .filter_map(
                |key| match table.declared(key, PageWidth::from(80_u32), Form::Explicit) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                },
            )
            .collect();
        assert_eq!(
            keyed,
            ["Counter.T", "Counter.T", "Counter.T"],
            "every declaration keyed in the source reads the atom by its path, never the \
             representation; the abstract type itself carries no form key"
        );
    }

    #[test]
    fn a_sign_member_answers_under_the_sorts_before_it()
    {
        let source = SourceText::from(
            "sign Cat {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  oper id : (a \
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
            .filter_map(
                |key| match table.declared(key, PageWidth::from(80_u32), Form::Explicit) {
                    Maybe::Present(Declared::Typed(spelled)) => {
                        Some(String::from(spelled.as_ref()))
                    },
                    Maybe::Present(Declared::Refused(_)) | Maybe::Absent(_) => None,
                },
            )
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
}
