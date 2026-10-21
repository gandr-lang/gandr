//! Declaration descriptions read from molded syntax, before core decoding.
//!
//! # Descriptions and native data
//!
//! `data`, `codata` and `theory` declarations are also read into checked
//! descriptions, and their operation and rule members into cells. A `data` form
//! keeps one producer of its signature, the native reading (the `lower::native`
//! module); the description route owns its members and decodes every other
//! described family.
//!
//! # Declarations read into descriptions
//!
//! `description::elaborate_descriptions` reads top-level `data`, `codata` and
//! `theory` declarations, and those a mutual block `rec { … }` holds, in source
//! order, into checked descriptions. Typed family parameters and
//! classifiers are retained separately from the description code. Constructor
//! results must name the declared family with the same parameter variables, in
//! order; declared value-index positions stay expressions rather than being
//! read as field types. A malformed member earns its own diagnostic without
//! removing readable siblings. The report retains structured well-formedness
//! diagnostics and their available source spans.
//!
//! # One producer for a data form
//!
//! A `data` form has one producer of its signature: the native reading (the
//! `lower::native` module), which lowers it to `DeclarationOutcome::Data`,
//! enters its constructors and compiles the matches over it. The description
//! route reads the same form beside it and owns what the native reading passes
//! over. Its `oper` and `rule` members become description and cell entries, and
//! a refusal among them is a held declaration at the member's own span under
//! the family's name. It neither replaces the family's native signature nor
//! consumes the declarations after the block. Every other described family with
//! a classifier — `codata` — is admitted at its own position and decoded from
//! its description by `decode_signature`, under all family parameters, with
//! later applications keeping the family's admission identity. The decoder's
//! refusal, `CodataNu` for codata, refuses that family alone, at its span. An
//! attribute block written before an admitted family decorates it, as one
//! before a `data` family does, so a corpus fixture states the refusal it
//! expects
//! (`description::tests::an_attribute_block_decorates_the_codata_declaration_after_it`).
//!
//! **Choice.** One producer per declaration form. The description decoder could
//! produce `data` signatures as well, but two producers for one form let a
//! native signature and a decoded one disagree about the same family, and only
//! the native reading enters constructors and compiles matches. The
//! alternatives were the decoder as the sole producer, which must first
//! reproduce native constructor entry and match compilation, and both producers
//! behind an agreement check, which reads every data family twice. A nominal
//! native family is preserved rather than replaced by a structural coproduct or
//! an opaque value declaration, and descriptive polarity stays separate from
//! core representability: a readable `codata` description is not silently
//! reinterpreted as a positive record. **Reversal.** A decoder that agrees with
//! the native reading on every data form, constructors and matches included,
//! can replace it as the producer. Further core readings arrive only with their
//! formation and checking rules.
//!
//! Witnesses:
//! `description::tests::native_data_keeps_telescope_and_nominal_heads`,
//! `description::tests::member_refusals_keep_their_spans_and_other_declarations`,
//! `description::tests::a_codata_declaration_lowers_to_its_signature`,
//! `lower::native::tests::operation_and_rule_members_are_left_to_the_description_route`,
//! and the description reader's declaration and refusal witnesses in
//! `description::tests`.
//!
//! # A family its code cannot carry
//!
//! The description code is first-order: a field is a type the code names or a
//! recursive reference to the family. A generator whose field is a universe, a
//! function or a type naming an earlier field has no code. A family with such a
//! generator and no `oper` or `rule` member is left whole to the native
//! reading: the route records no description and no refusal, only a
//! [`NativeFamily`] holding where each generator is written, so a face still
//! answers at its constructors (`crate::described`); the family's eliminator is
//! the native one. A family that writes an operation or a rule keeps the
//! refusal at the field, because its members are this route's to carry and
//! they cannot be carried without a code.
//!
//! **Choice.** The native reading owns what the code cannot carry. The
//! alternatives were a higher-order code (a `Π` former over a type,
//! Dybjer–Setzer style), which widens the levitated code and every reader of it
//! for families that need no member, and a refusal at every such field, which
//! refuses a family the checker admits. **Reversal.** A code former for a
//! function or universe field, with its decoder and its readers, lets this
//! route describe the family and lifts the rule-carrying case with it
//! (`description::tests::a_family_its_code_cannot_carry_is_left_to_the_native_reading`).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::ParamDesc;
use gandr_theory_levitation::PrimTy;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::ValueTypeRef;
use gandr_theory_levitation::ValueTypeView;
use gandr_theory_levitation::WfDiagnostic;
use quenchant_shape::shape::Maybe;

use crate::LoweringRefusal;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::unit::SourceIndex;
use crate::unit::Unit;

/// A finite multiplicity decorating a field.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Multiplicity(pub u64);

/// A field's declared usage, retained in the description.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DescriptionGrade
{
    /// A finite usage bound.
    Finite(Multiplicity),
    /// Unrestricted use.
    Omega,
}

/// Why a written declaration or member has no description.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptionFault
{
    /// The written shape is incomplete.
    Malformed,
    /// The parser repaired the declaration's form: the declaration's one
    /// refusal, whatever its reading would add.
    Repaired
    {
        /// The repair, read where it stands.
        repaired: crate::form::Repaired,
        /// The form the repair is reported against when it stands among the
        /// declaration's own children.
        form: crate::FormName,
    },
    /// Family parameters must be typed and the head must declare its index
    /// arity.
    FamilyHead,
    /// Constructor result must apply its own family uniformly.
    NonUniformResult,
    /// Function-valued fields have no first-order description code.
    HigherOrderField,
    /// A field whose type names a field before it has no first-order
    /// description code: the code's fields are independent.
    DependentField,
    /// A constructor must use the generator judgment spelling.
    GeneratorJudgment,
    /// The member belongs to another declaration polarity.
    MemberPolarity,
    /// A type shape has no symbolic first-order reference.
    TypeShape,
    /// The retired rule arrow has no rewrite-face reading.
    RetiredRuleArrow,
    /// The retired operation lead is not a synonym for an operation member.
    RetiredOperation,
    /// The native interpreter refused a well-formed description leaf.
    NativeDecode(gandr_core_term::description::DecodeError),
    /// The description checker refused the declaration.
    IllFormed(WfDiagnostic),
    /// A ruled signature reached an explicit surface or cell boundary.
    Signature(crate::circuit::SignatureFault),
}

/// The field refusals that mark the first-order code's limit rather than a
/// fault of the source: the native reading admits each such field.
const UNCODED: [DescriptionFault; 3] = [
    DescriptionFault::HigherOrderField,
    DescriptionFault::DependentField,
    DescriptionFault::TypeShape,
];

/// What the route reads a declaration form as.
enum Read
{
    /// A description whose members the route carries.
    Described(alloc::boxed::Box<DescribedDeclaration>),
    /// A data family the native reading owns whole.
    Native(alloc::boxed::Box<NativeFamily>),
}

/// A generator judgment as read.
struct Generator
{
    /// The constructor's description, or the first field its first-order code
    /// cannot carry.
    ctor: Result<CtorDesc<DescriptionGrade>, DescriptionDiagnostic>,
    /// Where the judgment's name, fields and result are written.
    written: written::WrittenConstructor,
}

/// A data family the native reading owns whole.
///
/// A generator of it the first-order code cannot carry, and it writes no
/// operation or rule for a description to carry, so the route keeps only
/// where its members are written.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeFamily
{
    /// Its name tile.
    pub named: Placed,
    /// Its name.
    pub name: Name,
    /// The parameter binders it writes.
    pub parameters: Vec<FamilyParameter>,
    /// Where each of its constructors is written, in declaration order.
    pub written: written::WrittenMembers,
}

/// A member-local refusal; siblings remain inspectable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescriptionDiagnostic
{
    /// Exact written site of the refusal.
    pub span: ByteSpan,
    /// Semantic refusal, independent of diagnostic wording.
    pub fault: DescriptionFault,
}

impl DescriptionDiagnostic
{
    /// Keep the source location when presenting a description refusal to the
    /// ordinary module consumer. The description report retains the full cause.
    ///
    /// # Specification
    /// - ensures: the module refusal covers exactly the diagnostic's source
    ///   site; a reserved glyph is a reserved form, a form the route parses and
    ///   does not read yet (an operation filler or a fillerless higher cell) an
    ///   unadmitted one, a feed no observation guards its own refusal, and
    ///   every other fault a malformed form.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused middle member cannot erase either
    ///   neighboring member, and an unguarded feed, a reversible glyph and a
    ///   cycle keep three classes apart.
    /// - witness: `description::tests::member_refusals_keep_their_spans_and_other_declarations`
    /// - witness: `description::theory::tests::theory_declines_and_malformed_wiring_are_refused_apart`
    #[spec(ensures: |result| result.span() == Maybe::Present(self.span))]
    pub(crate) fn lowering_refusal(&self) -> LoweringRefusal<'static>
    {
        let unread = |boundary| LoweringRefusal::OutOfFragment {
            span: self.span,
            form: crate::FormName::DECLARATION,
            sort: crate::FragmentSort::Declaration,
            boundary,
        };
        match self.fault {
            DescriptionFault::Repaired { repaired, form } => repaired.refusal(form),
            DescriptionFault::HigherOrderField
            | DescriptionFault::DependentField
            | DescriptionFault::TypeShape
            | DescriptionFault::NativeDecode(_)
            | DescriptionFault::Signature(
                crate::circuit::SignatureFault::OperationFiller
                | crate::circuit::SignatureFault::HigherCell,
            ) => unread(crate::FragmentBoundary::Unadmitted),
            DescriptionFault::Signature(crate::circuit::SignatureFault::BareFeedback { rule }) => {
                LoweringRefusal::BareFeedback {
                    span: self.span,
                    rule,
                }
            },
            DescriptionFault::Signature(crate::circuit::SignatureFault::Reversible) => {
                unread(crate::FragmentBoundary::Reserved)
            },
            DescriptionFault::Malformed
            | DescriptionFault::FamilyHead
            | DescriptionFault::NonUniformResult
            | DescriptionFault::GeneratorJudgment
            | DescriptionFault::MemberPolarity
            | DescriptionFault::RetiredRuleArrow
            | DescriptionFault::RetiredOperation
            | DescriptionFault::IllFormed(_)
            | DescriptionFault::Signature(_) => LoweringRefusal::MalformedForm {
                span: self.span,
                form: crate::FormName::DECLARATION,
                fault: crate::FormFault::MisplacedTile,
            },
        }
    }
}

/// A named family binder with its written classifier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FamilyParameter
{
    /// The binder tile, retained for source-backed native resolution.
    pub named: Placed,
    /// The bound name.
    pub name: Name,
    /// Its written classifier, for native telescope lowering.
    pub classifier: Placed,
}

quenchant_shape::reason_enum! {
    /// Why a description declaration has no ordinary family classifier.
    pub mod family_classifier {
        /// A description judgment, not a native value-family declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A `theory` block declares its sorts and cells inside the description.
            Signature,
            /// A top-level `oper` declares one operation by its circuit.
            Circuit,
        }
    }
}

/// A description and its core-lowering provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescribedDeclaration
{
    /// The declaration's syntax location.
    pub at: Placed,
    /// Its name tile.
    pub named: Placed,
    /// Checked description vocabulary; diagnostics remain in the report.
    pub description: TheoryDesc<DescriptionGrade>,
    /// Written operation members, indexed exactly as `description.opers`.
    pub operation_spans: Vec<ByteSpan>,
    /// The parameter classifiers retained for native decoding.
    pub parameters: Vec<FamilyParameter>,
    /// The written native family classifier; a `theory` block has none.
    pub classifier: Maybe<Placed, family_classifier::Absent>,
    /// What a `theory` block presents to the signature of its models; a family
    /// or a top-level operation presents none.
    pub presentation: crate::model::Presented,
    /// Where the members are written.
    pub written: written::WrittenMembers,
}

impl DescribedDeclaration
{
    /// The written rules, in rule order, each with the arrow it stated.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn rules(&self) -> impl Iterator<Item = written::SurfaceRule<'_>>
    {
        self.description
            .rules
            .iter()
            .zip(&self.written.faces)
            .map(|(face, written)| written::SurfaceRule { face, written })
    }
}

/// Descriptions and member-local refusals in declaration order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DescriptionReport
{
    /// Readable declarations, including their readable siblings after a
    /// refusal.
    pub declarations: Vec<DescribedDeclaration>,
    /// Every located refusal.
    pub diagnostics: Vec<DescriptionDiagnostic>,
    /// The data families the native reading owns whole, in declaration order.
    pub natives: Vec<NativeFamily>,
}

/// A nullary observation or a parameterized observation boundary.
enum Observation
{
    /// A result code at the family's polarity, and where it is written.
    Nullary(CtorDesc<DescriptionGrade>, written::WrittenObservation),
    /// An observation with explicit input ports and one result port.
    Parameterized(gandr_theory_levitation::OperDesc),
}

/// Borrowed syntax used by description readers.
struct Reader<'tree, 'source>
{
    /// Grammar interpreting the molded nodes.
    grammar: &'tree Pbg,
    /// Parsed source.
    tree: &'tree SyntaxTree<'source>,
}

/// A grammar tile spelling, distinct from source names.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Spelling(&'static str);

/// Whether a member's next piece is the tile a spelling names.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct TileSeen(bool);

/// The source text a syntax location covers.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct Written<'text>(&'text str);

/// A forward-only view over one written member.
struct Run<'pieces>
{
    /// The shared source-piece cursor.
    cursor: crate::form::Cursor<'pieces>,
    /// Provenance for missing syntax.
    span: ByteSpan,
}

impl<'pieces> Run<'pieces>
{
    /// Start a member reader.
    ///
    /// # Specification
    /// trivial.
    fn new(
        rest: &'pieces [Piece],
        span: ByteSpan,
    ) -> Self
    {
        Self {
            cursor: crate::form::Cursor::new(rest, span),
            span,
        }
    }

    /// Borrow the unread member suffix.
    ///
    /// # Specification
    /// trivial.
    fn remaining(&self) -> &'pieces [Piece]
    {
        self.cursor.remaining()
    }

    /// The bytes the next piece covers, or the member span when none remains.
    ///
    /// # Specification
    /// trivial.
    fn here(&self) -> ByteSpan
    {
        self.cursor.here()
    }

    /// Inspect the next grammar tile without advancing.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        spelling: Spelling,
    ) -> TileSeen
    {
        TileSeen(
            matches!(self.cursor.peek(), Maybe::Present(Piece::Tile { label, .. }) if label.as_ref() == spelling.0),
        )
    }

    /// Consume a matching tile and preserve all other input.
    ///
    /// # Specification
    /// - ensures: consumes exactly one matching tile, otherwise nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration witnesses distinguish consumed
    ///   punctuation from operands.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    #[spec(captures: before = self.remaining().len(), ensures: |result| self.remaining().len() == before.saturating_sub(usize::from(result.0)))]
    fn eat(
        &mut self,
        spelling: Spelling,
    ) -> TileSeen
    {
        if !self.at(spelling).0 {
            return TileSeen(false);
        }
        let _read = self.cursor.read();
        TileSeen(true)
    }

    /// Read the next written node or locate missing syntax.
    ///
    /// # Specification
    /// - ensures: consumes one piece and returns its original location.
    /// - fails: missing syntax returns `Malformed` at the member span.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` when the run is exhausted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing result and ordinary constructor witnesses
    ///   separate empty and nonempty runs.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    #[spec(captures: before = self.remaining().len(), ensures: |result| result.is_ok() == (before != 0))]
    fn take(&mut self) -> Result<Placed, DescriptionDiagnostic>
    {
        match self.cursor.read() {
            Maybe::Present(piece) => Ok(piece.placed()),
            Maybe::Absent(_) => Err(self.fault(DescriptionFault::Malformed)),
        }
    }

    /// Locate a member-local refusal.
    ///
    /// # Specification
    /// trivial.
    const fn fault(
        &self,
        fault: DescriptionFault,
    ) -> DescriptionDiagnostic
    {
        DescriptionDiagnostic {
            span: self.span,
            fault,
        }
    }
}

/// Read data and codata declarations, retaining every readable sibling, over
/// `tree` laid out as `unit`.
///
/// # Specification
/// - requires: `grammar` interprets `tree`, and `unit` lays out its text.
/// - ensures: declarations and diagnostics follow source order; unreadable
///   members never disappear without a located refusal; descriptions run
///   through `check_desc`. A declaration whose own form the parser repaired
///   carries exactly one diagnostic, [`DescriptionFault::Repaired`] at the
///   repair: a parse error is reported alone, never beside the refusals its
///   repaired reading would raise. An `include` reads the blocks its source
///   sees ([`Sight`]).
/// - fails: grammar lookup failures return the existing lowering refusal.
/// - panics: none.
///
/// # Errors
/// Returns a grammar or molded-node refusal from `read_pieces`.
///
/// # Adequacy
/// - hypothesis: L3 — exact constructor codes, refusal spans and surviving
///   siblings distinguish a dropped member, a substituted field and an
///   incorrectly global refusal; a `theory` with a keyword in a member's
///   classifier slot is refused once, at the keyword.
/// - witness: `description::tests::data_lowering_preserves_constructor_fields`
/// - witness: `lower::tests::a_keyword_in_a_classifier_slot_is_read_with_its_offer_293`
#[inline]
#[spec(ensures: |result| result.as_ref().map_or(true, |report| report.declarations.iter().all(|entry| tree.node(entry.at.node).is_some())))]
pub fn elaborate_descriptions<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
) -> Result<DescriptionReport, LoweringRefusal<'source>>
{
    if tree.grammar() != grammar.fingerprint() {
        return Err(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: grammar.fingerprint(),
        });
    }
    let mut report = DescriptionReport::default();
    elaborate_roots(
        grammar,
        tree,
        tree.roots(),
        NominalSerial::from(0_u64),
        &mut report,
        Sight {
            unit,
            prior: &BTreeMap::new(),
        },
    )?;

    Ok(report)
}

/// What a reading's `include`s may name besides its own declarations: the
/// unit its sources stand in, and the declarations read before it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Sight<'held>
{
    /// The unit the sources stand in.
    pub unit: &'held Unit,
    /// The declarations read before the roots this reading reads, by their
    /// nodes: a resumed document's closure's.
    pub prior: &'held BTreeMap<NodeIndex, DescribedDeclaration>,
}

/// The declarations an `include` written in one source may name.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub(crate) struct Visible<'held>
{
    /// Those of the including source read before it, in reading order.
    own: Vec<&'held DescribedDeclaration>,
    /// Those of the sources it imports unqualified, in reading order, each
    /// with its source.
    imported: Vec<(SourceIndex, &'held DescribedDeclaration)>,
}

impl<'held> Visible<'held>
{
    /// The declarations of `read` a declaration of `source` sees, `source`
    /// importing `imports` unqualified.
    ///
    /// # Specification
    /// - requires: `read` is in reading order.
    /// - ensures: `own` holds the declarations of `read` in `source`, and
    ///   `imported` those in a source of `imports`, both in the order of
    ///   `read`; every other declaration is passed over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration of a source not imported is not seen.
    /// - witness: `tests::namespace::an_include_reads_the_theories_its_source_imports_1224`
    #[spec(ensures: |ret| ret.own.iter().all(|declaration| unit.source_at(declaration.at.span.start()) == source)
        && ret.imported.iter().all(|&(from, declaration)| from != source && imports.contains(&from)
            && unit.source_at(declaration.at.span.start()) == from))]
    fn of(
        unit: &Unit,
        source: SourceIndex,
        imports: &BTreeSet<SourceIndex>,
        read: impl Iterator<Item = &'held DescribedDeclaration>,
    ) -> Self
    {
        let mut visible = Self::default();
        for declaration in read {
            let from = unit.source_at(declaration.at.span.start());
            if from == source {
                visible.own.push(declaration);
            }
            else if imports.contains(&from) {
                visible.imported.push((from, declaration));
            }
        }
        visible
    }
}

/// Read the data and codata declarations under `roots` into `report`, the
/// first of them numbered `first`, retaining every readable sibling.
///
/// # Specification
/// - requires: `grammar` interprets `tree`, `roots` are roots of `tree`, and
///   `sight` lays them out after its prior declarations.
/// - ensures: as [`elaborate_descriptions`], over the declarations under
///   `roots` in their order, each appended to `report` after what it holds and
///   numbered `first` and on in that order. An `include` names a `theory` block
///   of its own source read before it, or else of one source it imports
///   unqualified, among `sight`'s prior declarations and those read here.
/// - provides: the description reading of a document laid after a closure whose
///   declarations were read before.
/// - fails: as [`elaborate_descriptions`].
/// - panics: none.
///
/// # Errors
/// As [`elaborate_descriptions`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`elaborate_descriptions`]; a document resumed after
///   its closure numbers its declarations as the whole unit's reading does.
/// - witness: `description::tests::data_lowering_preserves_constructor_fields`
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[spec(
    captures: before = report.declarations.len(),
    ensures: |result| result.is_err() || report.declarations.len() >= before,
)]
pub(crate) fn elaborate_roots<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    roots: &[NodeIndex],
    first: NominalSerial,
    report: &mut DescriptionReport,
    sight: Sight<'_>,
) -> Result<(), LoweringRefusal<'source>>
{
    let reader = Reader { grammar, tree };
    let imports = crate::module::unqualified_imports(grammar, tree, roots, sight.unit);
    let none = BTreeSet::new();
    // The declarations in source order: a mutual block's members are read in
    // its place, as declarations of their own.
    let mut pending: Vec<_> = roots.iter().flat_map(|&root| tree.children(root)).collect();
    pending.reverse();
    while let Some(position) = pending.pop() {
        let Some(node) = tree.node(position)
        else {
            continue;
        };
        let at = Placed::of(position, node);
        let mut pieces = Pieces::new();
        read_pieces(grammar, tree, position, &mut pieces)?;
        if matches!(shape_of(grammar, node)?, Shape::Form { name, .. } if name == crate::FormName::MUTUAL)
        {
            pending.extend(pieces.pieces.iter().rev().filter_map(|piece| match *piece {
                Piece::Operand(member) => Some(member.node),
                Piece::Tile { .. } => None,
            }));
            continue;
        }
        let mut run = Run::new(&pieces.pieces, at.span);
        let serial = NominalSerial::from(
            u64::from(first)
                .saturating_add(u64::try_from(report.declarations.len()).unwrap_or(u64::MAX)),
        );
        let reported = report.diagnostics.len();
        let declaration = if run.eat(Spelling("data")).0 {
            reader.declaration(
                at,
                &mut run,
                DeclPolarity::Data,
                serial,
                &mut report.diagnostics,
            )
        }
        else if run.eat(Spelling("codata")).0 {
            reader.declaration(
                at,
                &mut run,
                DeclPolarity::Codata,
                serial,
                &mut report.diagnostics,
            )
        }
        else if run.eat(Spelling("theory")).0 {
            let source = sight.unit.source_at(at.span.start());
            let visible = Visible::of(
                sight.unit,
                source,
                imports.get(&source).unwrap_or(&none),
                sight.prior.values().chain(&report.declarations),
            );
            reader
                .signature(at, &mut run, serial, &visible, &mut report.diagnostics)
                .map(|declaration| Read::Described(alloc::boxed::Box::new(declaration)))
        }
        else if run.eat(Spelling("oper")).0 {
            reader
                .circuit_declaration(at, &mut run, serial, &mut report.diagnostics)
                .map(|declaration| Read::Described(alloc::boxed::Box::new(declaration)))
        }
        else {
            continue;
        };
        if let Maybe::Present(repair) = pieces.repair {
            // A declaration whose form carries a parse error reports that error
            // alone: what its reading of the repaired form refused follows from
            // the repair, so it is dropped with the reading's own diagnostics.
            report.diagnostics.truncate(reported);
            report.diagnostics.push(DescriptionDiagnostic {
                span: repair.span,
                fault: DescriptionFault::Repaired {
                    repaired: repair,
                    form: match shape_of(grammar, node)? {
                        Shape::Form { name, .. } => name,
                        Shape::Root | Shape::Layout | Shape::Repair(_) => {
                            crate::FormName::DECLARATION
                        },
                    },
                },
            });
            if let Ok(Read::Described(declaration)) = declaration {
                report.declarations.push(*declaration);
            }
            continue;
        }
        match declaration {
            Ok(Read::Native(family)) => report.natives.push(*family),
            Ok(Read::Described(declaration)) => {
                for diagnostic in gandr_theory_levitation::check_desc(&declaration.description) {
                    let span = match diagnostic.span {
                        Maybe::Present(position) => ByteSpan::new(
                            usize::from(position.start).into(),
                            usize::from(position.end).into(),
                        )
                        .unwrap_or(at.span),
                        Maybe::Absent(_) => at.span,
                    };
                    report.diagnostics.push(DescriptionDiagnostic {
                        span,
                        fault: DescriptionFault::IllFormed(diagnostic),
                    });
                }
                report.declarations.push(*declaration);
            },
            Err(diagnostic) => report.diagnostics.push(diagnostic),
        }
    }
    Ok(())
}

impl Reader<'_, '_>
{
    /// Source text at a validated syntax location.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &self,
        at: Placed,
    ) -> Written<'_>
    {
        Written(self.tree.fragment(at.node).map_or("", <&str>::from))
    }

    /// Read a nested syntax form through the shared molded-piece reader.
    ///
    /// # Specification
    /// - ensures: successful pieces preserve their own-rule labels and order.
    /// - fails: malformed grammar or repair returns a located refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for unreadable or repaired forms.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested applications distinguish operands from inline
    ///   punctuation.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    #[spec(ensures: |result| result.as_ref().map_or(true, |pieces| pieces.iter().all(|piece| self.tree.node(piece.placed().node).is_some())))]
    fn pieces(
        &self,
        at: Placed,
    ) -> Result<Vec<Piece>, DescriptionDiagnostic>
    {
        let mut read = Pieces::new();
        if read_pieces(self.grammar, self.tree, at.node, &mut read).is_err() {
            return Err(DescriptionDiagnostic {
                span: at.span,
                fault: DescriptionFault::Malformed,
            });
        }
        if let Maybe::Present(repair) = read.repair {
            return Err(DescriptionDiagnostic {
                span: repair.span,
                fault: DescriptionFault::Malformed,
            });
        }
        Ok(read.pieces)
    }

    /// Read a family head and every member independently.
    ///
    /// # Specification
    /// - ensures: preserves typed parameters, constructor order and polarity; a
    ///   data family a generator of which the first-order code cannot carry — a
    ///   universe, a function or a field naming one before it — is read as a
    ///   [`NativeFamily`], every generator's written form kept, when it writes
    ///   no operation and no rule, and keeps the generator's refusal otherwise.
    /// - fails: malformed family heads decline the declaration; malformed
    ///   members append local refusals without deleting siblings.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `FamilyHead` or `Malformed` when the head cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — member-local and family-wide failures have different
    ///   surviving declarations, and a W-shaped family with and without a rule
    ///   separate the native reading from the refusal.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    /// - witness: `description::tests::a_family_its_code_cannot_carry_is_left_to_the_native_reading`
    #[spec(ensures: |result| result.as_ref().map_or(true, |entry| match *entry {
        | Read::Described(ref entry) => entry.description.polarity == polarity,
        | Read::Native(_) => polarity == DeclPolarity::Data,
    }))]
    fn declaration(
        &self,
        at: Placed,
        run: &mut Run<'_>,
        polarity: DeclPolarity,
        serial: NominalSerial,
        diagnostics: &mut Vec<DescriptionDiagnostic>,
    ) -> Result<Read, DescriptionDiagnostic>
    {
        let named = run.take()?;
        let family = Name::from(self.text(named).0);
        let mut parameters = Vec::new();
        if run.eat(Spelling("(")).0 {
            while !run.eat(Spelling(")")).0 {
                let name = run.take()?;
                if !run.eat(Spelling(":")).0 {
                    return Err(run.fault(DescriptionFault::FamilyHead));
                }
                let classifier = run.take()?;
                parameters.push(FamilyParameter {
                    named: name,
                    name: Name::from(self.text(name).0),
                    classifier,
                });
                if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                    return Err(run.fault(DescriptionFault::FamilyHead));
                }
            }
        }
        if !run.eat(Spelling(":")).0 {
            return Err(run.fault(DescriptionFault::FamilyHead));
        }
        let classifier = run.take()?;
        let indices = self.index_arity(classifier)?;
        if !run.eat(Spelling("{")).0 {
            return Err(run.fault(DescriptionFault::FamilyHead));
        }
        let mut ctors = Vec::new();
        let mut operations = Vec::new();
        let mut operation_spans = Vec::new();
        let mut rules = Vec::new();
        let mut written = written::WrittenMembers::default();
        // A generator the first-order code cannot carry, held until the
        // members are read: it refuses only a family whose operations or
        // rules the description must carry.
        let mut uncoded = Vec::new();
        // Every generator as written, coded or not, for a family the native
        // reading owns whole.
        let mut generators = Vec::new();
        for member in split_members(run.remaining()) {
            let Some(first) = member.first()
            else {
                continue;
            };
            let last = member.last().unwrap_or(first);
            let span = ByteSpan::new(first.placed().span.start(), last.placed().span.end())
                .unwrap_or_else(|_inverted| first.placed().span);
            let mut member = Run::new(member, span);
            if member.at(Spelling("}")).0 {
                continue;
            }
            let result = if member.eat(Spelling("rule")).0 {
                self.rule(&mut member).map(|(rule, face)| {
                    rules.push(rule);
                    written.faces.push(face);
                })
            }
            else if member.eat(Spelling("oper")).0 {
                if polarity == DeclPolarity::Codata {
                    Err(member.fault(DescriptionFault::MemberPolarity))
                }
                else {
                    self.operation(&mut member).map(|(operation, ports)| {
                        operations.push(operation);
                        operation_spans.push(span);
                        written.operations.push(ports);
                    })
                }
            }
            else if member.eat(Spelling("op")).0 {
                Err(member.fault(DescriptionFault::RetiredOperation))
            }
            else {
                match polarity {
                    // A cell `name : a <-> a` between terms is the native
                    // reading's: it mints the words of the path type at its
                    // point, which the description does not carry.
                    DeclPolarity::Data if member.at(Spelling("identifier")).0 => Ok(()),
                    DeclPolarity::Data => self
                        .generator(&mut member, &family, &parameters, indices)
                        .map(|generator| {
                            generators.push(generator.written.clone());
                            match generator.ctor {
                                Ok(ctor) => {
                                    ctors.push(ctor);
                                    written.constructors.push(generator.written);
                                },
                                Err(diagnostic) => uncoded.push(diagnostic),
                            }
                        }),
                    DeclPolarity::Codata => self.observation(&mut member, &family).map(
                        |observation| match observation {
                            Observation::Nullary(ctor, observed) => {
                                ctors.push(ctor);
                                written.observations.push(observed);
                            },
                            Observation::Parameterized(operation) => {
                                operations.push(operation);
                                operation_spans.push(span);
                            },
                        },
                    ),
                }
            };
            if let Err(diagnostic) = result {
                diagnostics.push(diagnostic);
            }
        }
        if !uncoded.is_empty() {
            if operations.is_empty() && rules.is_empty() {
                return Ok(Read::Native(alloc::boxed::Box::new(NativeFamily {
                    named,
                    name: family,
                    parameters,
                    written: written::WrittenMembers {
                        constructors: generators,
                        ..written::WrittenMembers::default()
                    },
                })));
            }
            diagnostics.extend(uncoded);
        }
        let params: Vec<_> = parameters
            .iter()
            .map(|parameter| {
                ParamDesc::new(
                    parameter.name.clone(),
                    DescriptionGrade::Finite(Multiplicity(1)),
                    Attrs::empty(),
                )
            })
            .collect();
        let description = TheoryDesc::new(
            NominalId::new(serial, family),
            params,
            ctors,
            operations,
            rules,
            polarity,
            Attrs::empty(),
        );
        Ok(Read::Described(alloc::boxed::Box::new(
            DescribedDeclaration {
                at,
                named,
                description,
                operation_spans,
                parameters,
                classifier: Maybe::Present(classifier),
                presentation: Maybe::Absent(crate::model::presentation::Absent::Family),
                written,
            },
        )))
    }

    /// Read a generator judgment and require a uniform result head, keeping
    /// where its name, each field and its result are written.
    ///
    /// # Specification
    /// - ensures: each payload field keeps its type, grade and order; the
    ///   written constructor holds the name tile, one port per field, its name
    ///   tile when written, the result's bytes and each of its arguments'. A
    ///   higher-order or universe field, or one whose type names a field before
    ///   it, leaves the constructor uncoded with the first such field's
    ///   refusal, and the judgment is still read whole.
    /// - fails: nonuniform results and incomplete judgments are located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first unreadable field or result refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reordered or instantiated parameters cannot pass head
    ///   uniformity, and an uncoded field keeps the fields and result after it
    ///   written.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    /// - witness: `description::tests::a_family_its_code_cannot_carry_is_left_to_the_native_reading`
    #[spec(ensures: |result| result.as_ref().map_or(true, |read| read.ctor.as_ref().map_or(true, |ctor| ctor.result == *family)))]
    fn generator(
        &self,
        run: &mut Run<'_>,
        family: &Name,
        parameters: &[FamilyParameter],
        indices: family::IndexArity,
    ) -> Result<Generator, DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.fault(DescriptionFault::GeneratorJudgment));
        }
        let mut fields = Vec::new();
        let mut ports = Vec::new();
        // The first field the first-order code cannot carry.
        let mut uncoded = None;
        let port = |named: Maybe<ByteSpan, written::port_name::Absent>, sort: Placed| {
            written::WrittenPort {
                named,
                binders: Vec::new(),
                sort: written::WrittenSort {
                    span: sort.span,
                    indices: Vec::new(),
                },
            }
        };
        let result = if run.eat(Spelling("(")).0 {
            let mut bound = Vec::new();
            while !run.eat(Spelling(")")).0 {
                let grade = self.grade(run)?;
                let first = run.take()?;
                let (ty, label) = if run.eat(Spelling(":")).0 {
                    (run.take()?, Maybe::Present(first))
                }
                else {
                    (first, Maybe::Absent(written::port_name::Absent::Unnamed))
                };
                match self.field(ty, family, grade, &bound) {
                    Ok((field, _written)) => fields.push(field),
                    Err(diagnostic) if UNCODED.contains(&diagnostic.fault) => {
                        let _first = uncoded.get_or_insert(diagnostic);
                    },
                    Err(diagnostic) => return Err(diagnostic),
                }
                ports.push(port(label.map(|binder| binder.span), ty));
                if let Maybe::Present(binder) = label {
                    bound.push(binder);
                }
                if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                    return Err(run.fault(DescriptionFault::Malformed));
                }
            }
            if !run.eat(Spelling("-->")).0 {
                return Err(run.fault(DescriptionFault::GeneratorJudgment));
            }
            run.take()?
        }
        else {
            let first = run.take()?;
            if run.eat(Spelling("-->")).0 {
                match self.field(first, family, DescriptionGrade::Finite(Multiplicity(1)), &[
                ]) {
                    Ok((field, _written)) => fields.push(field),
                    Err(diagnostic) if UNCODED.contains(&diagnostic.fault) => {
                        let _first = uncoded.get_or_insert(diagnostic);
                    },
                    Err(diagnostic) => return Err(diagnostic),
                }
                ports.push(port(
                    Maybe::Absent(written::port_name::Absent::Unnamed),
                    first,
                ));
                run.take()?
            }
            else {
                first
            }
        };
        let arguments = self.uniform_result(result, family, parameters, indices)?;
        let attrs = self.attrs(run)?;
        run.end()?;
        Ok(Generator {
            ctor: uncoded.map_or_else(
                || {
                    Ok(CtorDesc::new(
                        self.text(named).0,
                        Code::product_of(fields),
                        family.clone(),
                        attrs,
                    ))
                },
                Err,
            ),
            written: written::WrittenConstructor {
                named: named.span,
                fields: ports,
                result: result.span,
                arguments,
            },
        })
    }

    /// Read a codata observation, retaining its declared input boundary.
    ///
    /// # Specification
    /// - ensures: retains observation name, grade and result code, and for a
    ///   nullary observation where its name and each node of its type are
    ///   written.
    /// - fails: constructor and operation leads refuse the wrong polarity.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `MemberPolarity` or the field's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — observation witnesses distinguish lowercase
    ///   observations from data generators.
    /// - witness: `description::tests::codata_observations_preserve_their_codes`
    #[spec(ensures: |result| match result {
        Ok(Observation::Nullary(ref ctor, ref written)) => ctor.result == *family && !written.ty.nodes.is_empty(),
        Ok(Observation::Parameterized(ref operation)) => operation.arity.outputs.len() == 1,
        Err(_) => true,
    })]
    fn observation(
        &self,
        run: &mut Run<'_>,
        family: &Name,
    ) -> Result<Observation, DescriptionDiagnostic>
    {
        if run.at(Spelling("oper")).0 || run.at(Spelling("constructor")).0 {
            return Err(run.fault(DescriptionFault::MemberPolarity));
        }
        let grade = self.grade(run)?;
        let named = run.take()?;
        if run.eat(Spelling("(")).0 {
            let (inputs, _written) = self.ports(run)?;
            if !run.eat(Spelling(":")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            let result = run.take()?;
            let output =
                gandr_theory_levitation::SortRef::new(self.text(named).0, self.text(result).0);
            let attrs = self.attrs(run)?;
            run.end()?;
            return Ok(Observation::Parameterized(
                gandr_theory_levitation::OperDesc::new(
                    self.text(named).0,
                    gandr_theory_levitation::BridgeArity::single_output(inputs, output),
                    attrs,
                ),
            ));
        }
        if !run.eat(Spelling(":")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let ty = run.take()?;
        let (code, written) = self.field(ty, family, grade, &[])?;
        let attrs = self.attrs(run)?;
        run.end()?;
        Ok(Observation::Nullary(
            CtorDesc::new(self.text(named).0, code, family.clone(), attrs),
            written::WrittenObservation {
                named: named.span,
                ty: written,
            },
        ))
    }

    /// Read a finite or unrestricted field grade.
    ///
    /// # Specification
    /// - ensures: absent annotation denotes one; written annotations are
    ///   retained.
    /// - fails: a finite grade outside u64 is malformed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for an overflowing numeral.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite and unrestricted observations distinguish
    ///   annotation erasure.
    /// - witness: `description::tests::codata_observations_preserve_their_codes`
    #[spec(captures: before = run.remaining().len(), ensures: |result| result.is_ok() || run.remaining().len() < before)]
    fn grade(
        &self,
        run: &mut Run<'_>,
    ) -> Result<DescriptionGrade, DescriptionDiagnostic>
    {
        if run.eat(Spelling("ω")).0 {
            return Ok(DescriptionGrade::Omega);
        }
        if run.at(Spelling("number")).0 {
            let at = run.take()?;
            let value = self
                .text(at)
                .0
                .parse::<u64>()
                .map_err(|_error| run.fault(DescriptionFault::Malformed))?;
            return Ok(DescriptionGrade::Finite(Multiplicity(value)));
        }
        Ok(DescriptionGrade::Finite(Multiplicity(1)))
    }

    /// Interpret a first-order field, recognizing the recursive family head,
    /// and keep where each node of its type is written.
    ///
    /// # Specification
    /// - requires: `bound` holds the binders of the fields before this one.
    /// - ensures: self references become recursive code, whatever their indices
    ///   name, and other fields retain symbolic types; the written term is the
    ///   type's, as [`Self::type_reference`] keeps it.
    /// - fails: unreadable type forms return their located refusal, and a
    ///   symbolic type naming a binder of `bound` refuses as dependent.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `TypeShape`, `HigherOrderField`, `DependentField` or
    /// `Malformed`.
    ///
    /// # Termination
    /// - reason: the dependency walk is a `while let` loop over an explicit
    ///   stack, not recursion.
    /// - measure: the reference's nodes not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — recursive and primitive fields distinguish var from
    ///   field, and a field naming the one before it is told from one naming a
    ///   parameter.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    /// - witness: `description::tests::a_family_its_code_cannot_carry_is_left_to_the_native_reading`
    #[spec(ensures: |result| result.as_ref().map_or(true, |&(ref code, _)| code.recursive_sorts().all(|sort| sort == family)))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `bound` holds the binders written before one field"
        )
    )]
    fn field(
        &self,
        at: Placed,
        family: &Name,
        grade: DescriptionGrade,
        bound: &[Placed],
    ) -> Result<(Code<DescriptionGrade>, written::WrittenTerm), DescriptionDiagnostic>
    {
        let (reference, written) = self.type_reference(at)?;
        if &reference.head_name() == family {
            return Ok((Code::var(family.clone()), written));
        }
        let mut pending = Vec::from([reference.to_node()]);
        while let Some(node) = pending.pop() {
            match node.view() {
                ValueTypeView::Param(name)
                    if bound
                        .iter()
                        .any(|&binder| self.text(binder).0 == name.as_ref()) =>
                {
                    return Err(DescriptionDiagnostic {
                        span: at.span,
                        fault: DescriptionFault::DependentField,
                    });
                },
                ValueTypeView::Param(_) | ValueTypeView::Prim(_) => {},
                ValueTypeView::Ctor { args, .. } => pending.extend(args),
            }
        }
        Ok((Code::field(reference, grade, Attrs::empty()), written))
    }

    /// Read symbolic first-order types with an explicit postorder stack, and
    /// keep where each node is written.
    ///
    /// # Specification
    /// - ensures: applications preserve the head and argument order without
    ///   Rust recursion. The written term holds one node per node of the type,
    ///   in pre-order, each at its own bytes and an application with its
    ///   head's.
    /// - fails: function fields, universes and unknown type shapes are refused
    ///   at their written node.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `HigherOrderField`, `TypeShape` or `Malformed`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested applications, the four primitives, universes
    ///   and function fields separate supported shapes and order.
    /// - witness: `description::tests::data_lowering_preserves_constructor_fields`
    /// - witness: `description::tests::a_family_its_code_cannot_carry_is_left_to_the_native_reading`
    /// - witness: `description::tests::a_field_reads_each_primitive_and_each_applied_argument`
    #[spec(ensures: |result| result.as_ref().map_or_else(|_| self.tree.node(at.node).is_some(), |&(_, ref written)| written.nodes.first().is_some_and(|node| node.span == at.span)))]
    fn type_reference(
        &self,
        at: Placed,
    ) -> Result<(ValueTypeRef, written::WrittenTerm), DescriptionDiagnostic>
    {
        let mut pending = vec![TypeFrame::Read(at)];
        let mut values = Vec::new();
        let mut written = written::WrittenTerm::default();
        while let Some(frame) = pending.pop() {
            match frame {
                TypeFrame::Read(at) => {
                    let pieces = self.pieces(at)?;
                    if let [Piece::Tile { label, .. }] = *pieces.as_slice() {
                        let text = self.text(at).0;
                        let ty = match (label.as_ref(), text) {
                            (_, "Integer") => ValueTypeRef::prim(PrimTy::Integer),
                            (_, "String") => ValueTypeRef::prim(PrimTy::StringTy),
                            (_, "Boolean") => ValueTypeRef::prim(PrimTy::Boolean),
                            (_, "Unit") => ValueTypeRef::prim(PrimTy::Unit),
                            ("type_variable", _) => ValueTypeRef::param(text),
                            ("type_identifier", "Type") => {
                                return Err(DescriptionDiagnostic {
                                    span: at.span,
                                    fault: DescriptionFault::TypeShape,
                                });
                            },
                            ("type_identifier", _) => ValueTypeRef::ctor(text, []),
                            _ => {
                                return Err(DescriptionDiagnostic {
                                    span: at.span,
                                    fault: DescriptionFault::TypeShape,
                                });
                            },
                        };
                        values.push(ty);
                        written.nodes.push(written::WrittenNode {
                            span: at.span,
                            head: Maybe::Absent(written::head::Absent::Leaf),
                        });
                        continue;
                    }
                    if pieces.iter().any(|piece| matches!(piece, Piece::Tile { label, .. } if matches!(label.as_ref(), "->" | "=>"))) {
                        return Err(DescriptionDiagnostic { span: at.span, fault: DescriptionFault::HigherOrderField });
                    }
                    let mut run = Run::new(&pieces, at.span);
                    let head = run.take()?;
                    if !run.eat(Spelling("(")).0 {
                        return Err(run.fault(DescriptionFault::TypeShape));
                    }
                    let mut args = Vec::new();
                    while !run.eat(Spelling(")")).0 {
                        args.push(run.take()?);
                        if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                            return Err(run.fault(DescriptionFault::TypeShape));
                        }
                    }
                    written.nodes.push(written::WrittenNode {
                        span: at.span,
                        head: Maybe::Present(head.span),
                    });
                    pending.push(TypeFrame::Apply(
                        Name::from(self.text(head).0),
                        ArgumentCount(args.len()),
                    ));
                    pending.extend(args.into_iter().rev().map(TypeFrame::Read));
                },
                TypeFrame::Apply(head, count) => {
                    let Some(start) = values.len().checked_sub(count.0)
                    else {
                        return Err(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::Malformed,
                        });
                    };
                    let ty = ValueTypeRef::ctor(head, values.drain(start ..));
                    values.push(ty);
                },
            }
        }
        let value = values.pop().ok_or(DescriptionDiagnostic {
            span: at.span,
            fault: DescriptionFault::TypeShape,
        })?;
        Ok((value, written))
    }
}

/// A symbolic application arity.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct ArgumentCount(usize);

/// A pending symbolic type interpretation.
enum TypeFrame
{
    /// Read one nested type node.
    Read(Placed),
    /// Assemble the previously read argument suffix.
    Apply(Name, ArgumentCount),
}

/// Borrow member runs, splitting only at outermost separators.
///
/// # Specification
/// - ensures: nested commas and semicolons stay within their member.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — multi-field constructors distinguish nested from member
///   separators, and a member a repaired close ends is kept.
/// - witness: `description::tests::data_lowering_preserves_constructor_fields`
/// - witness: `description::tests::a_block_left_open_keeps_the_member_before_its_missing_close`
#[spec(ensures: |result| result.iter().all(|member| !member.is_empty()))]
fn split_members(pieces: &[Piece]) -> Vec<&[Piece]>
{
    let mut result = Vec::new();
    let mut rest = pieces;
    let mut start = 0_usize;
    let mut depth = 0_usize;
    for (index, piece) in pieces.iter().enumerate() {
        let Piece::Tile { label, .. } = *piece
        else {
            continue;
        };
        match label.as_ref() {
            "}" if depth == 0 => {
                let count = index.saturating_sub(start);
                if let Some(member) = rest.get(.. count)
                    && !member.is_empty()
                {
                    result.push(member);
                }
                return result;
            },
            ";" | "," if depth == 0 => {
                let count = index.saturating_sub(start);
                if let Some((member, suffix)) = rest.split_at_checked(count) {
                    if !member.is_empty() {
                        result.push(member);
                    }
                    rest = suffix.get(1 ..).unwrap_or(&[]);
                }
                start = index.saturating_add(1);
            },
            "(" | "[" | "{" | "#{" => depth = depth.saturating_add(1),
            ")" | "]" | "}" => depth = depth.saturating_sub(1),
            _ => {},
        }
    }
    if !rest.is_empty() {
        result.push(rest);
    }
    result
}

mod family;

mod members;

mod theory;

pub mod written;

#[cfg(test)]
mod tests;
