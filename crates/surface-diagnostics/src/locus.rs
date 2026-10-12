//! Where a report points and what it says: the loci each producer recorded
//! for a refusal, and the prose each refusal is titled with.
//!
//! # A locus is read, never searched for
//!
//! A lowering refusal and a corpus refusal carry their spans. A checker
//! refusal names core nodes, and the lowering's origin table maps each node it
//! minted back to the syntax that produced it; a node the checker minted
//! itself, such as a type it synthesised, has no origin, and its annotation is
//! left out rather than guessed. A refusal the checker raises about a
//! declaration as a whole is located at the declaration.
//!
//! # A type without a locus is still spelled
//!
//! The types a checker refusal compares were spelled when its module was
//! judged; a [`Comparison`] reads them back by node, so a synthesised type the
//! label cannot point at is still named in it.
//!
//! # A refusal's nested reasons are the judgements it stood inside
//!
//! The composition keeps, for each refused body, the value and computation
//! judgements the refusal stood inside, outermost first. Each one whose term
//! the origin table locates is a [`Reason`]: its term's bytes, and whether the
//! term was checked, against which type, or synthesised. A reason at the
//! primary locus, or at bytes an outer reason already marks, says nothing the
//! report does not, and is left out; a term with no origin is left out rather
//! than located at a guess.

use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::CoreNode;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Mismatch;
use gandr_core_checker::Pending;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::compared;
use gandr_kernel_term::DescentRefusal;
use gandr_kernel_term::OccurrenceSite;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::ExpectationFault;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::Surviving;
use gandr_surface_dispatcher::Spellings;
use gandr_surface_dispatcher::spelling;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::culprit::Culprit;
use crate::report::Unsettlement;
use crate::report::report_span;

quenchant_shape::reason_enum! {
    /// Why a context slot holds no annotation.
    pub mod report_context {
        /// The reason a context slot is empty.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal names no second locus for this slot.
            Unnamed,
            /// The refusal names a node the origin table holds nothing for:
            /// one the checker minted itself.
            Unrecorded,
            /// The span recorded lies outside the source's text, or splits
            /// one of its characters.
            OutsideText,
        }
    }
}

/// What an annotation says about the bytes it marks.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Label
{
    /// What the refused bytes are: the primary locus of a refusal.
    Culprit(Culprit),
    /// What the unsettlement of a declaration that produced no refusal rests
    /// on: its primary locus.
    Unsettled(Unsettlement),
    /// The obligations a declaration leaves unsettled: the primary locus of a
    /// goal and of a declaration unsettled by its obligations.
    Surviving(Surviving),
    /// The first occurrence a duplicate repeats.
    First,
    /// The declaration of a member named before it.
    Declared,
    /// The type a mismatched term was checked against.
    Expected,
    /// The type a mismatched term synthesised.
    Synthesised,
    /// The type a rule met where it required a former of another shape.
    Met(ExpectedShape),
    /// A declared name or a binder over a builtin: the primary locus of a
    /// shadowing warning.
    Shadows,
}

impl fmt::Display for Label
{
    /// Writes the label's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the annotation's role or required shape, retaining any
    ///   surviving-obligation counts; propagates a destination failure.
    /// - provides: the causal label beside a marked source span.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mismatch and duplicate snippets expose located
    ///   labels; all required shapes expose their surface notation. These
    ///   observations distinguish lost notation and label placement, not
    ///   arbitrary wording or failing destinations.
    /// - witness: `diagnostics::diagnostics::a_labeled_context_retains_its_locus_and_cause`
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Culprit(culprit) => fmt::Display::fmt(&culprit, f),
            | Self::Unsettled(unsettlement) => fmt::Display::fmt(&unsettlement, f),
            | Self::Surviving(surviving) => write!(f, "surviving obligations: {surviving}"),
            | Self::First => f.write_str("first written here"),
            | Self::Declared => f.write_str("declared here"),
            | Self::Expected => f.write_str("the type it is checked against"),
            | Self::Synthesised => f.write_str("the type it synthesises"),
            | Self::Met(wanted) => write!(f, "the type met, where {} is required", Shape(wanted)),
            | Self::Shadows => f.write_str("shadows a builtin"),
        }
    }
}

/// The types a checker refusal compares, as the composition spelled them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Comparison<'step>
{
    /// The type the rule required.
    pub expected: Maybe<&'step str, spelling::Absent>,
    /// The type the rule met.
    pub found: Maybe<&'step str, spelling::Absent>,
}

/// A comparison of no types.
const UNCOMPARED: Comparison<'static> = Comparison {
    expected: Maybe::Absent(spelling::Absent::Unspelled),
    found: Maybe::Absent(spelling::Absent::Unspelled),
};

impl<'step> Comparison<'step>
{
    /// The types `refusal` compares, read from `spellings`.
    ///
    /// # Specification
    /// - requires: `spellings` was spelled over the arena `refusal` names.
    /// - ensures: a checker refusal's expected and found sides are the
    ///   spellings of the nodes [`CheckRefusal::compared`] names, each absent
    ///   where it names none or the spellings hold none; a lowering or corpus
    ///   refusal compares no types.
    /// - provides: the comparison a primary label carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch reads both spellings in their roles,
    ///   and a lowering refusal reads none.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::a_mismatch_label_spells_both_types`
    #[spec(ensures: |ret| match refusal {
        Refusal::Checking(checked) => {
            let side = |node: Maybe<TypeNode, _>| match node {
                Maybe::Present(node) => spellings.get(node).map(AsRef::as_ref),
                Maybe::Absent(_) => Maybe::Absent(spelling::Absent::Unspelled),
            };
            ret.expected == side(checked.compared().expected) && ret.found == side(checked.compared().found)
        },
        Refusal::Lowering(_) | Refusal::Corpus(_) => ret == UNCOMPARED,
    })]
    pub(crate) fn of(
        refusal: Refusal<'_>,
        spellings: &'step Spellings,
    ) -> Self
    {
        let Refusal::Checking(checked) = refusal
        else {
            return UNCOMPARED;
        };
        let compared = checked.compared();
        let side = |node: Maybe<TypeNode, compared::Absent>| match node {
            | Maybe::Present(node) => spellings.get(node).map(AsRef::as_ref),
            | Maybe::Absent(_) => Maybe::Absent(spelling::Absent::Unspelled),
        };
        Self {
            expected: side(compared.expected),
            found: side(compared.found),
        }
    }

    /// A comparison of no types: the one every report but a checker
    /// refusal's carries.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn none() -> Self
    {
        UNCOMPARED
    }
}

impl fmt::Display for Comparison<'_>
{
    /// Writes the types compared: `expected` and `found`, either alone, or
    /// nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes ``expected `E`, found `F` `` for both sides, the one
    ///   side alone when only it is spelled, and nothing when neither is;
    ///   propagates a destination failure.
    /// - provides: the comparison clause of a primary label.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch shows both sides in their roles and
    ///   a shape mismatch the found side alone.
    /// - witness: `diagnostics::diagnostics::a_mismatch_label_spells_both_types`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match (self.expected, self.found) {
            | (Maybe::Present(expected), Maybe::Present(found)) => {
                write!(f, "expected `{expected}`, found `{found}`")
            },
            | (Maybe::Present(expected), Maybe::Absent(_)) => write!(f, "expected `{expected}`"),
            | (Maybe::Absent(_), Maybe::Present(found)) => write!(f, "found `{found}`"),
            | (Maybe::Absent(_), Maybe::Absent(_)) => Ok(()),
        }
    }
}

/// The label under a report's primary locus: what its bytes are, and the types
/// its refusal compares.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrimaryLabel<'step>
{
    /// What the bytes are.
    pub label: Label,
    /// The types the refusal compares.
    pub comparison: Comparison<'step>,
}

impl fmt::Display for PrimaryLabel<'_>
{
    /// Writes the label, then the comparison after a colon when it compares
    /// any type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the label's text, followed by `: ` and the comparison
    ///   when either side is spelled; propagates a destination failure.
    /// - provides: the one text a terminal underline and an editor message both
    ///   show.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mismatch label carries its types after its text,
    ///   and an unresolved name's label carries none.
    /// - witness: `diagnostics::diagnostics::a_mismatch_label_spells_both_types`
    /// - witness: `diagnostics::diagnostics::refusals_of_one_class_label_what_their_locus_is`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.label, f)?;
        if self.comparison == UNCOMPARED {
            return Ok(());
        }
        write!(f, ": {}", self.comparison)
    }
}

/// How a judgement a refusal stood inside judged its term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Judging<'step>
{
    /// The term was checked against a type, spelled when the composition
    /// could spell it.
    Checked(Maybe<&'step str, spelling::Absent>),
    /// The term's type was synthesised.
    Synthesised,
}

/// One judgement a refusal stood inside, at its term's bytes: a nested reason.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reason<'step>
{
    /// The bytes of the term under judgement.
    pub span: ByteSpan,
    /// How the term was judged.
    pub judging: Judging<'step>,
}

impl<'step> Reason<'step>
{
    /// The located reasons `pending` gives, outermost first.
    ///
    /// # Specification
    /// - requires: `origins` and `spellings` were built over the arena
    ///   `pending` names.
    /// - ensures: one reason per judgement of `pending` whose term `origins`
    ///   locates, in order, except one at `primary` or at bytes an earlier
    ///   reason marks; each checked against the spelling of its expected type,
    ///   absent where the spellings hold none, or synthesised.
    /// - provides: the nested reasons a report renders beside its primary
    ///   locus.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a force refused inside a thunk keeps the thunk as a
    ///   checked reason with its type and drops the force, which is the primary
    ///   locus; a mismatch at a declaration's whole body keeps none.
    /// - witness: `diagnostics::diagnostics::a_refusal_names_the_judgements_it_stood_inside`
    #[spec(ensures: |ret| ret.len() <= pending.len()
        && ret.iter().all(|reason| primary != Maybe::Present(reason.span))
        && ret.iter().enumerate().all(|(at, reason)| ret.iter().take(at).all(|outer| outer.span != reason.span)))]
    pub(crate) fn trail(
        pending: &[Pending],
        origins: &OriginTable,
        spellings: &'step Spellings,
        primary: Maybe<ByteSpan, report_span::Absent>,
    ) -> Vec<Self>
    {
        let mut reasons: Vec<Self> = Vec::with_capacity(pending.len());
        for judgement in pending {
            let Maybe::Present(span) = node(origins, CoreNode::Term(judgement.term))
            else {
                continue;
            };
            if primary == Maybe::Present(span) || reasons.iter().any(|outer| outer.span == span) {
                continue;
            }
            let judging = match judgement.expected {
                | Maybe::Present(expected) => {
                    Judging::Checked(spellings.get(expected).map(AsRef::as_ref))
                },
                | Maybe::Absent(_) => Judging::Synthesised,
            };
            reasons.push(Self { span, judging });
        }
        reasons
    }
}

impl fmt::Display for Reason<'_>
{
    /// Writes the judgement the reason stands for, as a clause beginning
    /// `while`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes ``while checking this against `T` `` for a term
    ///   checked against a spelled type, `while checking this` for one whose
    ///   type has no spelling, and `while synthesising the type of this` for a
    ///   synthesised one; propagates a destination failure.
    /// - provides: the label a terminal writes under the reason's bytes and an
    ///   editor shows at its related location.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checked thunk and a synthesised application render
    ///   their two clauses.
    /// - witness: `diagnostics::diagnostics::a_refusal_names_the_judgements_it_stood_inside`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.judging {
            | Judging::Checked(Maybe::Present(expected)) => {
                write!(f, "while checking this against `{expected}`")
            },
            | Judging::Checked(Maybe::Absent(_)) => f.write_str("while checking this"),
            | Judging::Synthesised => f.write_str("while synthesising the type of this"),
        }
    }
}

/// One marked span and what it says.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Annotation
{
    /// The bytes marked.
    pub span: ByteSpan,
    /// What the mark says.
    pub label: Label,
}

/// Every locus one report marks: the primary one, when the producer recorded
/// it, and at most two context loci beside it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Annotations
{
    /// The locus the report is about.
    pub primary: Maybe<Annotation, report_span::Absent>,
    /// The loci that explain it, in the order the refusal names them.
    pub context: [Maybe<Annotation, report_context::Absent>; 2_usize],
}

/// No context locus.
const UNNAMED: [Maybe<Annotation, report_context::Absent>; 2_usize] = [
    Maybe::Absent(report_context::Absent::Unnamed),
    Maybe::Absent(report_context::Absent::Unnamed),
];

impl Annotations
{
    /// A primary locus at `span` saying `label`, with no context.
    ///
    /// # Specification
    /// trivial.
    pub const fn at(
        span: ByteSpan,
        label: Label,
    ) -> Self
    {
        Self {
            primary: Maybe::Present(Annotation { span, label }),
            context: UNNAMED,
        }
    }

    /// The loci of a declaration whose expectation `stated` states no
    /// verdict, the declaration spanning `declaration`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the primary locus is the attribute the fault names — the
    ///   second of two conflicting expectations, with the first as context —
    ///   labelled as a malformed expectation; a statement that is a verdict
    ///   falls back to `declaration`.
    /// - provides: the loci of a malformed expectation, read from the fault.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conflicting pair exposes the primary and context
    ///   roles and a one-span fault its attribute; a verdict exposes the
    ///   fallback.
    /// - witness: `locus::tests::a_malformed_expectation_points_at_its_attribute`
    #[spec(ensures: |ref ret| match *stated {
        Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }) =>
            *ret == Self {
                primary: Maybe::Present(Annotation { span: second, label: Label::Unsettled(Unsettlement::Malformed) }),
                context: [Maybe::Present(Annotation { span: first, label: Label::First }), Maybe::Absent(report_context::Absent::Unnamed)],
            },
        Stated::Malformed(ExpectationFault::UnknownRefusal { span }
            | ExpectationFault::NegativeObligations { span }
            | ExpectationFault::ObligationsBeyondRange { span }) =>
            *ret == Self::at(span, Label::Unsettled(Unsettlement::Malformed)),
        Stated::Verdict(_) => *ret == Self::at(declaration, Label::Unsettled(Unsettlement::Malformed)),
    })]
    pub fn malformed(
        stated: &Stated,
        declaration: ByteSpan,
    ) -> Self
    {
        let label = Label::Unsettled(Unsettlement::Malformed);
        match *stated {
            | Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }) => {
                Self {
                    primary: Maybe::Present(Annotation {
                        span: second,
                        label,
                    }),
                    context: [
                        Maybe::Present(Annotation {
                            span: first,
                            label: Label::First,
                        }),
                        Maybe::Absent(report_context::Absent::Unnamed),
                    ],
                }
            },
            | Stated::Malformed(
                ExpectationFault::UnknownRefusal { span }
                | ExpectationFault::NegativeObligations { span }
                | ExpectationFault::ObligationsBeyondRange { span },
            ) => Self::at(span, label),
            | Stated::Verdict(_) => Self::at(declaration, label),
        }
    }

    /// The loci of a lowering refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the primary locus is the span the lowering rejected, labelled
    ///   with what those bytes are, and is absent for the two refusals about
    ///   the run rather than a position; a duplicate declaration, import alias
    ///   or attribute marks its first occurrence as context, and a member named
    ///   before its declaration marks that declaration.
    /// - provides: the loci of a lowering refusal, whether it refused a
    ///   declaration or the source as a whole.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real duplicate and unresolved-name reports expose the
    ///   rejected span and first-occurrence role. A run-budget refusal exposes
    ///   the no-source-location boundary. Other lowering constructors are not
    ///   individually enumerated.
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `locus::tests::run_refusals_have_no_invented_source_locus`
    #[spec(ensures: |ref ret| {
        let label = Label::Culprit(Culprit::of(Refusal::Lowering(refusal)));
        let located = match (refusal.span(), ret.primary) {
            (Maybe::Present(span), Maybe::Present(annotation)) =>
                annotation.span == span && annotation.label == label,
            (Maybe::Absent(_), Maybe::Absent(report_span::Absent::Run)) => true,
            _ => false,
        };
        located && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed)
            && match refusal {
                LoweringRefusal::DuplicateSignature { first, .. }
                | LoweringRefusal::DuplicateDefinition { first, .. }
                | LoweringRefusal::DuplicateImportAlias { first, .. }
                | LoweringRefusal::DuplicateAttribute { first, .. } =>
                    ret.context[0_usize] == Maybe::Present(Annotation { span: first, label: Label::First }),
                LoweringRefusal::ForwardMemberReference { declared, .. } =>
                    ret.context[0_usize] == Maybe::Present(Annotation { span: declared, label: Label::Declared }),
                _ => ret.context[0_usize] == Maybe::Absent(report_context::Absent::Unnamed),
            }
    })]
    pub fn lowering(refusal: LoweringRefusal<'_>) -> Self
    {
        let primary = match refusal.span() {
            | Maybe::Present(span) => Maybe::Present(Annotation {
                span,
                label: Label::Culprit(Culprit::of(Refusal::Lowering(refusal))),
            }),
            | Maybe::Absent(_) => Maybe::Absent(report_span::Absent::Run),
        };
        let context = match refusal {
            | LoweringRefusal::DuplicateSignature { first, .. }
            | LoweringRefusal::DuplicateDefinition { first, .. }
            | LoweringRefusal::DuplicateImportAlias { first, .. }
            | LoweringRefusal::DuplicateAttribute { first, .. } => Maybe::Present(Annotation {
                span: first,
                label: Label::First,
            }),
            | LoweringRefusal::ForwardMemberReference { declared, .. } => {
                Maybe::Present(Annotation {
                    span: declared,
                    label: Label::Declared,
                })
            },
            | LoweringRefusal::UnresolvedName { .. }
            | LoweringRefusal::UnresolvedDocLink { .. }
            | LoweringRefusal::UnresolvedTypeHead { .. }
            | LoweringRefusal::ShadowedBuiltin { .. }
            | LoweringRefusal::OutOfFragment { .. }
            | LoweringRefusal::GradedBridge { .. }
            | LoweringRefusal::MalformedLiteral { .. }
            | LoweringRefusal::MalformedForm { .. }
            | LoweringRefusal::UnknownAttribute { .. }
            | LoweringRefusal::MissingPayload { .. }
            | LoweringRefusal::NonValuePayload { .. }
            | LoweringRefusal::IllTypedPayload { .. }
            | LoweringRefusal::UnknownMember { .. }
            | LoweringRefusal::UnreadAscription { .. }
            | LoweringRefusal::LowercaseModuleName { .. }
            | LoweringRefusal::NonExhaustiveMatch { .. }
            | LoweringRefusal::UnmarkedSelfReference { .. }
            | LoweringRefusal::MissingExit { .. }
            | LoweringRefusal::Unreachable { .. }
            | LoweringRefusal::BudgetExceeded { .. }
            | LoweringRefusal::GrammarMismatch { .. }
            | LoweringRefusal::UnknownMold { .. } => Maybe::Absent(report_context::Absent::Unnamed),
        };
        Self {
            primary,
            context: [context, Maybe::Absent(report_context::Absent::Unnamed)],
        }
    }

    /// The loci of `refusal`, raised against the declaration spanning
    /// `declaration`, its nodes located through `origins`.
    ///
    /// # Specification
    /// - requires: `origins` is the table of the lowering that minted the nodes
    ///   the checker judged.
    /// - ensures: a lowering refusal is located as [`Annotations::lowering`]
    ///   locates it and a corpus refusal at the attribute it refuses. A checker
    ///   refusal is located at the origin of the node it names: the mismatched
    ///   term, with the type it was checked against and the type it synthesised
    ///   as context; the term whose type lacks a shape, with the type met as
    ///   context; the checking-only form, the constant, the out-of-fragment
    ///   node, the unbound variable or the dangling node. A hole, an exhausted
    ///   allowance, an admission out of order and a machine invariant are about
    ///   the declaration as a whole and are located at `declaration`. A node
    ///   the table holds nothing for leaves its locus absent.
    /// - provides: the primary locus labelled with what the refused bytes are,
    ///   and its context.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lowering, corpus and checker fixtures expose the
    ///   producer's primary label and causal spans. Distinct origin records and
    ///   missing nodes distinguish wrong locations from missing metadata. Other
    ///   producer payloads are outside these finite fixtures.
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
    #[spec(ensures: |ref ret| {
        let label = Label::Culprit(Culprit::of(refusal));
        let labelled = match ret.primary {
            Maybe::Present(annotation) => annotation.label == label,
            Maybe::Absent(report_span::Absent::Run | report_span::Absent::Unrecorded) => true,
            Maybe::Absent(report_span::Absent::OutsideText) => false,
        };
        labelled && ret.context.iter().all(|slot| !matches!(*slot,
            Maybe::Absent(report_context::Absent::OutsideText)))
            && if let Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { span, .. }) = refusal {
                ret.primary == Maybe::Present(Annotation { span, label })
                    && ret.context == UNNAMED
            } else { true }
    })]
    pub fn refusal(
        refusal: Refusal<'_>,
        declaration: ByteSpan,
        origins: &OriginTable,
    ) -> Self
    {
        match refusal {
            | Refusal::Lowering(lowering) => Self::lowering(lowering),
            | Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { span, .. }) => {
                Self::at(span, Label::Culprit(Culprit::of(refusal)))
            },
            | Refusal::Checking(checking) => checked(checking, declaration, origins),
        }
    }
}

/// The loci of the checker refusal `refusal`.
///
/// # Specification
/// - requires: origins describe the nodes named by the refusal.
/// - ensures: node-specific refusals use recorded origins; missing origins
///   remain unrecorded. Context slots retain their causal roles. Whole-
///   declaration failures use the declaration span with no invented context.
/// - provides: raw checker loci before source-text validation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite typed origin tables separate recorded spans from
///   missing nodes. Computation mismatches and shape failures expose context
///   order; selected whole-declaration failures expose fallback precedence.
///   Other checker constructors are not individually enumerated.
/// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
/// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
/// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
/// - witness: `locus::tests::checker_fallbacks_preserve_causal_roles`
#[spec(ensures: |ref ret| {
    let label = Label::Culprit(Culprit::of(Refusal::Checking(refusal)));
    let labelled = match ret.primary {
        Maybe::Present(annotation) => annotation.label == label,
        Maybe::Absent(report_span::Absent::Unrecorded) => true,
        Maybe::Absent(report_span::Absent::Run | report_span::Absent::OutsideText) => false,
    };
    let role = |slot: &Maybe<Annotation, report_context::Absent>, wanted| match *slot {
        Maybe::Present(annotation) => annotation.label == wanted,
        Maybe::Absent(report_context::Absent::Unrecorded) => true,
        Maybe::Absent(report_context::Absent::Unnamed | report_context::Absent::OutsideText) => false,
    };
    labelled && match refusal {
        CheckRefusal::DataFieldLevel {..} | CheckRefusal::MissingRecordField {..} => role(&ret.context[0_usize],Label::Expected) && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::TypeMismatch(_) | CheckRefusal::SortMismatch { .. }
            | CheckRefusal::LevelMismatch { .. } | CheckRefusal::FamilyArgumentClassifier { .. } =>
            role(&ret.context[0_usize], Label::Expected) && role(&ret.context[1_usize], Label::Synthesised),
        CheckRefusal::DependentBind { .. } => role(&ret.context[0_usize], Label::Synthesised)
            && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::ShapeMismatch { wanted, .. } => role(&ret.context[0_usize], Label::Met(wanted))
            && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::NotSynthesisable { form: CheckingForm::Hole(_) }
            | CheckRefusal::NotADataType(_)
            | CheckRefusal::NegativeOccurrence(_) | CheckRefusal::NestedOccurrence(_)
            | CheckRefusal::IndexOccurrence(_) | CheckRefusal::NonUniformOccurrence(_)
            | CheckRefusal::CrossBlockReference { .. }
            | CheckRefusal::BudgetExceeded { .. } | CheckRefusal::AdmissionOrder { .. }
            | CheckRefusal::MachineInvariant => ret.primary == Maybe::Present(Annotation {
                span: declaration, label,
            }) && ret.context == UNNAMED,
        _ => ret.context == UNNAMED,
    }
})]
fn checked(
    refusal: CheckRefusal,
    declaration: ByteSpan,
    origins: &OriginTable,
) -> Annotations
{
    let label = Label::Culprit(Culprit::of(Refusal::Checking(refusal)));
    let (primary, context) = match refusal {
        | CheckRefusal::DataKindNotUniverse(at) | CheckRefusal::DataArgumentArity(at) => {
            (spanned(origins.value_type(at)), UNNAMED)
        },
        | CheckRefusal::DataFieldLevel { field, kind } => (spanned(origins.value_type(field)), [
            annotated(spanned(origins.value_type(kind)), Label::Expected),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        | CheckRefusal::UnknownConstructor { at, .. } | CheckRefusal::ConstructorArity(at) => {
            (spanned(origins.value(at)), UNNAMED)
        },
        | CheckRefusal::MissingRecordField { at, expected } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value_type(expected)), Label::Expected),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        | CheckRefusal::DependentStack { at, synthesised } => (spanned(origins.value(at)), [
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        | CheckRefusal::EffectSignatureConflict { at, .. } => {
            (spanned(origins.computation(at)), UNNAMED)
        },
        | CheckRefusal::TypeMismatch(Mismatch::Value {
            at,
            synthesised,
            expected,
        })
        | CheckRefusal::SortMismatch {
            at,
            synthesised,
            expected,
        }
        | CheckRefusal::LevelMismatch {
            at,
            synthesised,
            expected,
        }
        | CheckRefusal::FamilyArgumentClassifier {
            at,
            synthesised,
            expected,
            ..
        } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value_type(expected)), Label::Expected),
            annotated(spanned(origins.value_type(synthesised)), Label::Synthesised),
        ]),
        | CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected,
        }) => (spanned(origins.computation(at)), [
            annotated(spanned(origins.comp_type(expected)), Label::Expected),
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
        ]),
        | CheckRefusal::DependentBind { at, synthesised } => (spanned(origins.computation(at)), [
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        | CheckRefusal::ShapeMismatch { at, wanted, found } => {
            (node(origins, CoreNode::Term(at)), [
                annotated(node(origins, CoreNode::Type(found)), Label::Met(wanted)),
                Maybe::Absent(report_context::Absent::Unnamed),
            ])
        },
        | CheckRefusal::NotSynthesisable {
            form:
                CheckingForm::Reify(at)
                | CheckingForm::List(at)
                | CheckingForm::Injection(at)
                | CheckingForm::Thunk(at)
                | CheckingForm::StaticLambda(at),
        }
        | CheckRefusal::PathCode(at)
        | CheckRefusal::UnknownConstant { at, .. }
        | CheckRefusal::UnboundIndex { at, .. }
        | CheckRefusal::Undecided { at }
        | CheckRefusal::FamilyArity { at, .. }
        | CheckRefusal::StaticLambdaArgument { at } => (spanned(origins.value(at)), UNNAMED),
        | CheckRefusal::StaticClassifierExpected { found, .. } => {
            (spanned(origins.value_type(found)), UNNAMED)
        },
        | CheckRefusal::UnknownOperation { at }
        | CheckRefusal::HandlerCoverage { at }
        | CheckRefusal::ShiftWithoutReset { at }
        | CheckRefusal::NotSynthesisable {
            form:
                CheckingForm::Handle(at)
                | CheckingForm::Reset(at)
                | CheckingForm::Shift(at)
                | CheckingForm::With(at)
                | CheckingForm::Case(at)
                | CheckingForm::Split(at)
                | CheckingForm::Lambda(at)
                | CheckingForm::Return(at)
                | CheckingForm::Fixpoint(at),
        }
        | CheckRefusal::DescentNotReplayed { at, .. }
        | CheckRefusal::NonExhaustiveDataCase(at)
        | CheckRefusal::AbsentRecordField(at)
        | CheckRefusal::AbsentTupleComponent(at) => (spanned(origins.computation(at)), UNNAMED),
        | CheckRefusal::OutOfFragment { at: core, .. }
        | CheckRefusal::DanglingNode { node: core } => (node(origins, core), UNNAMED),
        | CheckRefusal::NotADataType(_)
        | CheckRefusal::NegativeOccurrence(_)
        | CheckRefusal::NestedOccurrence(_)
        | CheckRefusal::IndexOccurrence(_)
        | CheckRefusal::NonUniformOccurrence(_)
        | CheckRefusal::CrossBlockReference { .. }
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(_),
        }
        | CheckRefusal::BudgetExceeded { .. }
        | CheckRefusal::AdmissionOrder { .. }
        | CheckRefusal::MachineInvariant => return Annotations::at(declaration, label),
    };
    let primary = match primary {
        | Maybe::Present(span) => Maybe::Present(Annotation { span, label }),
        | Maybe::Absent(node_span::Absent::Unrecorded) => {
            Maybe::Absent(report_span::Absent::Unrecorded)
        },
    };
    Annotations { primary, context }
}

quenchant_shape::reason_enum! {
    /// Why a core node has no span.
    pub mod node_span {
        /// The reason a node is unlocated.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The origin table holds nothing for the node: the checker minted
            /// it, or another lowering did.
            Unrecorded,
        }
    }
}

/// The span of the syntax `origin` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: preserves a recorded origin's exact span; every absent origin
///   becomes an unrecorded node span, never a fabricated location.
/// - provides: a source span independent of the origin's provenance.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — recorded expected-type origins and missing synthesised
///   origins distinguish lost metadata from fabricated spans. Finite typed
///   tables also expose shifted records; arbitrary provenance histories are
///   outside these observations.
/// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
/// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
#[spec(ensures: |ret| match (origin, ret) {
    (Maybe::Present(held), Maybe::Present(span)) => span == held.span(),
    (Maybe::Absent(_), Maybe::Absent(node_span::Absent::Unrecorded)) => true,
    _ => false,
})]
fn spanned<Reason>(origin: Maybe<Origin, Reason>) -> Maybe<ByteSpan, node_span::Absent>
where
    Reason: Copy,
{
    match origin {
        | Maybe::Present(origin) => Maybe::Present(origin.span()),
        | Maybe::Absent(_) => Maybe::Absent(node_span::Absent::Unrecorded),
    }
}

/// The span of the syntax that produced `core`.
///
/// # Specification
/// - requires: origins are indexed under their typed core families.
/// - ensures: the span recorded for this node in its own family, or the
///   unrecorded reason when that family holds no origin for its identifier.
/// - provides: a location without guessing from another node or declaration.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite origin tables with colliding numeric family
///   positions and distinct spans expose shifted lookup. Unrecorded nodes
///   expose fabricated declaration fallbacks. Other table sizes and invalid
///   record insertion order are outside these fixtures.
/// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
/// - witness: `locus::tests::checker_fallbacks_preserve_causal_roles`
#[spec(ensures: |ret| {
    let origin = match core {
        CoreNode::Term(TermNode::Value(at)) => origins.value(at),
        CoreNode::Term(TermNode::Computation(at)) => origins.computation(at),
        CoreNode::Type(TypeNode::Value(at)) => origins.value_type(at),
        CoreNode::Type(TypeNode::Computation(at)) => origins.comp_type(at),
    };
    match (origin, ret) {
        (Maybe::Present(held), Maybe::Present(span)) => span == held.span(),
        (Maybe::Absent(_), Maybe::Absent(node_span::Absent::Unrecorded)) => true,
        _ => false,
    }
})]
fn node(
    origins: &OriginTable,
    core: CoreNode,
) -> Maybe<ByteSpan, node_span::Absent>
{
    match core {
        | CoreNode::Term(TermNode::Value(at)) => spanned(origins.value(at)),
        | CoreNode::Term(TermNode::Computation(at)) => spanned(origins.computation(at)),
        | CoreNode::Type(TypeNode::Value(at)) => spanned(origins.value_type(at)),
        | CoreNode::Type(TypeNode::Computation(at)) => spanned(origins.comp_type(at)),
    }
}

/// A context annotation saying `label` at `span`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a recorded span keeps the supplied causal label; an unrecorded
///   span remains an unrecorded context slot, never an unnamed one.
/// - provides: the distinction between absent metadata and no causal locus.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — expected and synthesised context slots expose role
///   substitution and the unnamed/unrecorded distinction. Shape contexts
///   exercise the required-shape label. Other source spans are outside these
///   finite fixtures.
/// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
/// - witness: `locus::tests::checker_fallbacks_preserve_causal_roles`
#[spec(ensures: |ret| match (span, ret) {
    (Maybe::Present(span), Maybe::Present(annotation)) =>
        annotation.span == span && annotation.label == label,
    (Maybe::Absent(node_span::Absent::Unrecorded), Maybe::Absent(report_context::Absent::Unrecorded)) => true,
    _ => false,
})]
fn annotated(
    span: Maybe<ByteSpan, node_span::Absent>,
    label: Label,
) -> Maybe<Annotation, report_context::Absent>
{
    match span {
        | Maybe::Present(span) => Maybe::Present(Annotation { span, label }),
        | Maybe::Absent(node_span::Absent::Unrecorded) => {
            Maybe::Absent(report_context::Absent::Unrecorded)
        },
    }
}

/// The prose a checker refusal is titled with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Checked(pub CheckRefusal);

impl fmt::Display for Checked
{
    /// Writes what the judgement refused, without the node ids the refusal
    /// carries, which the snippet locates instead.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the refusal's subject and semantic numeric payloads,
    ///   without exposing diagnostic-only node addresses; propagates a write
    ///   failure.
    /// - provides: the checker's diagnostic title.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — output text and destination failure cannot be
    ///   observed independently through the formatter argument.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — former titles distinguish subjects while remaining
    ///   invariant under node-address changes. Selected numeric refusals expose
    ///   payload order without pinning prose. Other refusal messages and
    ///   failing destinations are outside these observations.
    /// - witness: `locus::tests::former_titles_distinguish_subjects_not_node_addresses`
    /// - witness: `locus::tests::checker_titles_preserve_numeric_roles`
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            CheckRefusal::NotADataType(constant) => write!(f,"declaration {} is not an admitted datatype",usize::from(constant)),
            CheckRefusal::DataKindNotUniverse(_) => f.write_str("a datatype kind must be a value universe"),
            CheckRefusal::DataFieldLevel {..} => f.write_str("a constructor field exceeds the declared universe"),
            CheckRefusal::DataArgumentArity(_) => f.write_str("the datatype application has the wrong parameter count"),
            CheckRefusal::UnknownConstructor {tag,..} => write!(f,"constructor tag {} is absent from the datatype",usize::from(tag)),
            CheckRefusal::ConstructorArity(_) => f.write_str("the constructor has the wrong field count"),
            CheckRefusal::NonExhaustiveDataCase(_) => f.write_str("the data case must cover every constructor exactly once"),
            CheckRefusal::AbsentRecordField(_) => f.write_str("the record type has no such field"),
            CheckRefusal::AbsentTupleComponent(_) => f.write_str("the product type has no such component"),
            CheckRefusal::MissingRecordField {..} => f.write_str("the record omits a required field"),
            | CheckRefusal::UnknownOperation { .. } => f.write_str("the operation is absent from its inline interface"),
            | CheckRefusal::HandlerCoverage { .. } => f.write_str("handler clauses must cover their interface exactly once"),
            | CheckRefusal::ShiftWithoutReset { .. } => f.write_str("shift requires an enclosing reset answer type"),
            | CheckRefusal::DependentStack { .. } => f.write_str("the stack frame's result type mentions its discharged value binder"),
            | CheckRefusal::EffectSignatureConflict { .. } => f.write_str("two accumulated effect rows disagree on the operation types of a shared interface"),
            | CheckRefusal::PathCode(_) => f.write_str("a universe path requires a quoted closed first-order code"),
            | CheckRefusal::TypeMismatch(_) => f.write_str(
                "the type this term synthesises does not convert to the type it is checked against",
            ),
            | CheckRefusal::ShapeMismatch { wanted, .. } => {
                write!(f, "the rule here requires {}", Shape(wanted))
            },
            | CheckRefusal::NotSynthesisable { form } => write!(
                f,
                "{} stands where a type must be synthesised",
                match form {
                    | CheckingForm::Reify(_) => "a stack literal",
                    | CheckingForm::Handle(_) => "a handler",
                    | CheckingForm::Reset(_) => "a reset",
                    | CheckingForm::Shift(_) => "a shift",
                    | CheckingForm::With(_) => "a lazy pair",
                    | CheckingForm::Injection(_) => "an injection",
                    | CheckingForm::List(_) => "a List introduction",
                    | CheckingForm::Case(_) => "a case",
                    | CheckingForm::Split(_) => "a split",
                    | CheckingForm::Thunk(_) => "a thunk",
                    | CheckingForm::Lambda(_) => "a lambda",
                    | CheckingForm::Return(_) => "a return",
                    | CheckingForm::Hole(_) => "a hole",
                    | CheckingForm::StaticLambda(_) => "a type operator",
                    | CheckingForm::Fixpoint(_) => "a fixpoint",
                }
            ),
            | CheckRefusal::UnknownConstant { constant, .. } => write!(
                f,
                "the constant names admission position {}, which holds no declaration the context has a type for",
                usize::from(constant)
            ),
            | CheckRefusal::OutOfFragment { former, .. } => {
                write!(f, "the judgement has no rule for {}", Former(former))
            },
            | CheckRefusal::UnboundIndex { .. } => {
                f.write_str("the variable's index counts past every binder its zone holds")
            },
            | CheckRefusal::BudgetExceeded { budget } => {
                write!(f, "the judgement outran its allowance of {budget} steps")
            },
            | CheckRefusal::DanglingNode { .. } => {
                f.write_str("an id names no node of the arena the checking context reads")
            },
            | CheckRefusal::AdmissionOrder { constant, admitted } => write!(
                f,
                "admission position {} is not above position {}, already admitted",
                usize::from(constant),
                usize::from(admitted)
            ),
            | CheckRefusal::MachineInvariant => {
                f.write_str("the checking machine's bookkeeping disagreed with itself")
            },
            | CheckRefusal::SortMismatch { .. } => f.write_str(
                "the code's universe is of the other sort than the universe it is checked against",
            ),
            | CheckRefusal::LevelMismatch { .. } => f.write_str(
                "the code's universe stands at a level the universe it is checked against does not admit",
            ),
            | CheckRefusal::DependentBind { .. } => f.write_str(
                "the bind's continuation synthesises a type that mentions the value it binds",
            ),
            | CheckRefusal::Undecided { .. } => {
                f.write_str("the normaliser did not certify the unfolding of this code")
            },
            | CheckRefusal::FamilyArity {
                expected, actual, ..
            } => write!(
                f,
                "the type operator takes {} arguments, and this application passes {}",
                u32::from(expected),
                u32::from(actual)
            ),
            | CheckRefusal::FamilyArgumentClassifier { position, .. } => write!(
                f,
                "argument {} of this type operator is not classified by its parameter's domain",
                u32::from(position)
            ),
            | CheckRefusal::StaticLambdaArgument { .. } => f.write_str(
                "a type operator stands where a dynamic parameter needs a value, and it does not \
                 normalize away",
            ),
            | CheckRefusal::StaticClassifierExpected { .. } => f.write_str(
                "a type operator's classifier stands over a type that classifies no codes: \
                 neither a universe nor another such classifier",
            ),
            | CheckRefusal::NegativeOccurrence(site) => write!(
                f,
                "the declared type occurs under a function's domain in {}",
                Site(site)
            ),
            | CheckRefusal::NestedOccurrence(site) => write!(
                f,
                "the declared type occurs inside another type former in {}",
                Site(site)
            ),
            | CheckRefusal::IndexOccurrence(site) => write!(
                f,
                "the declared type occurs inside a term a type reads in {}",
                Site(site)
            ),
            | CheckRefusal::NonUniformOccurrence(site) => write!(
                f,
                "the declared type is applied to other arguments than its parameters in {}",
                Site(site)
            ),
            | CheckRefusal::CrossBlockReference { site, index } => write!(
                f,
                "{} names declaration {}, which follows this one",
                Site(site),
                usize::from(index)
            ),
            | CheckRefusal::DescentNotReplayed { reason, .. } => write!(
                f,
                "the fixpoint's structural-descent claim does not replay: {}",
                Descent(reason)
            ),
        }
    }
}

/// The former a rule required, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Shape(pub ExpectedShape);

impl fmt::Display for Shape
{
    /// Writes the former with its notation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the required former with its surface notation.
    /// - provides: shape information in a causal label or refusal title.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — located reports exercise the diagnostic consumer, not
    ///   exhaustive shape wording or destination failures.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            | ExpectedShape::Data => "a nominal datatype",
            | ExpectedShape::Record => "a record type",
            | ExpectedShape::Stack => "a stack type from input to output computation",
            | ExpectedShape::With => "a lazy pair of computation types",
            | ExpectedShape::PathUniverse => "a universe-path classifier `Path_U a b`",
            | ExpectedShape::Sum => "a sum type `A + B`",
            | ExpectedShape::List => "a List type `List A`",
            | ExpectedShape::Thunk => "a thunk type `+U C`",
            | ExpectedShape::Returner => "a returner `-F A`",
            | ExpectedShape::Arrow => "an arrow `A → C`",
            | ExpectedShape::Product => "an eager product `A * B`",
            | ExpectedShape::StaticPi => "a type operator's classifier `K -> J`",
        })
    }
}

/// A former the judgement has no rule for, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Former(pub UnadmittedFormer);

impl fmt::Display for Former
{
    /// Writes the former's name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the name of the unadmitted former.
    /// - provides: the subject of an out-of-fragment checker refusal.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite unadmitted-former vocabulary produces
    ///   distinct titles independent of node addresses. Collapsed subjects or
    ///   leaked addresses change an observation; exact prose and destination
    ///   failures are outside this contract's evidence.
    /// - witness: `locus::tests::former_titles_distinguish_subjects_not_node_addresses`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            | UnadmittedFormer::Reify => "a stack literal at the pure kernel boundary",
            | UnadmittedFormer::Stack => "a stack classifier at the pure kernel boundary",
            | UnadmittedFormer::Perform => "an effect request at the pure kernel boundary",
            | UnadmittedFormer::Handle => "an effect handler at the pure kernel boundary",
            | UnadmittedFormer::Resume => "a resumption at the pure kernel boundary",
            | UnadmittedFormer::Reset => "an answer delimiter at the pure kernel boundary",
            | UnadmittedFormer::Shift => "a continuation capture at the pure kernel boundary",
            | UnadmittedFormer::With => "a lazy pair at the pure kernel boundary",
            | UnadmittedFormer::Project => "a lazy-pair projection at the pure kernel boundary",
            | UnadmittedFormer::ValueLift => "an explicit universe lift of a value",
            | UnadmittedFormer::NumericLiteral => "a numeric literal",

            | UnadmittedFormer::NumericAtom => "the numeric base atom",

            | UnadmittedFormer::TypeLift => "a lift of a value type to a level not above its own",
            | UnadmittedFormer::Abstract => "a sealed abstract type",
            | UnadmittedFormer::SortParameter => "a universe over a sort parameter",
            | UnadmittedFormer::TopUniverse => "a universe at the greatest representable level",
            | UnadmittedFormer::StaticLambda => "a type operator",
            | UnadmittedFormer::EffectRow => "a nonempty effect row at the pure kernel boundary",
        })
    }
}

/// The parameter or field a data declaration's occurrence stands in, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Site(pub OccurrenceSite);

impl fmt::Display for Site
{
    /// Writes the site by its ordinals.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the parameter's position, or the field's position and
    ///   its constructor's tag.
    /// - provides: the place an occurrence refusal names.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field and a parameter site title their ordinals in
    ///   order, and each recursion refusal titles a distinct subject.
    /// - witness: `locus::tests::recursion_titles_name_their_site_and_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            | OccurrenceSite::Parameter(position) => {
                write!(f, "parameter {}", usize::from(position))
            },
            | OccurrenceSite::Field { tag, field } => write!(
                f,
                "field {} of constructor {}",
                usize::from(field),
                usize::from(tag)
            ),
        }
    }
}

/// The rule of the descent walk a claim failed, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Descent(pub DescentRefusal);

impl fmt::Display for Descent
{
    /// Writes the failed rule.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes what the descent walk did not find.
    /// - provides: the reason a descent refusal names.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each failed rule titles a distinct subject.
    /// - witness: `locus::tests::recursion_titles_name_their_site_and_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            | DescentRefusal::NotOverData => "its type is not a function out of a datatype",
            | DescentRefusal::NotCaseOnArgument => {
                "its body is not a case on its argument with one branch per constructor"
            },
            | DescentRefusal::BranchNotOverFields => {
                "a branch does not bind exactly its constructor's fields"
            },
            | DescentRefusal::UnguardedSelfReference => {
                "the recursive name stands other than at the head of a call"
            },
            | DescentRefusal::NonDescendingCall => {
                "a recursive call's argument is neither a field of the scrutinised constructor \
                 nor a function field's result"
            },
        })
    }
}

/// Source-location boundaries and semantic formatter payloads.
#[cfg(test)]
mod tests
{
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CoreNode;
    use gandr_core_checker::ExpectedShape;
    use gandr_core_checker::Mismatch;
    use gandr_core_checker::TermNode;
    use gandr_core_checker::TypeNode;
    use gandr_core_checker::UnadmittedFormer;
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DescentRefusal;
    use gandr_kernel_term::FieldPosition;
    use gandr_kernel_term::OccurrenceSite;
    use gandr_kernel_term::ParameterPosition;
    use gandr_surface_corpus::Refusal;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Origin;
    use gandr_surface_lowering::OriginTable;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::NodeIndex;
    use quenchant_shape::shape::Maybe;

    use super::Annotation;
    use super::Annotations;
    use super::Checked;
    use super::Culprit;
    use super::ExpectationFault;
    use super::Label;
    use super::Stated;
    use super::UNNAMED;
    use super::Unsettlement;
    use super::report_context;
    use super::report_span;

    #[test]
    fn refusal_locations_keep_origin_families_and_missing_nodes_distinct()
    {
        let spans: [ByteSpan; 8_usize] = core::array::from_fn(|index| {
            ByteSpan::new(
                ByteOffset::from(index * 10_usize),
                ByteOffset::from(index * 10_usize + 3_usize),
            )
            .expect("ordered fixture spans")
        });
        let recorded: [Origin; 8_usize] =
            core::array::from_fn(|index| Origin::new(NodeIndex::from(index), spans[index]));
        let mut arena = CoreArena::new();
        let values = [arena.value_unit(), arena.value_unit()];
        let computations = [
            arena.computation_return(values[0_usize]),
            arena.computation_return(values[1_usize]),
        ];
        let value_types = [arena.value_type_unit(), arena.value_type_unit()];
        let comp_types = [
            arena.comp_type_returner(value_types[0_usize]),
            arena.comp_type_returner(value_types[1_usize]),
        ];
        let mut origins = OriginTable::new();
        for index in 0_usize .. 2_usize {
            origins.record_value(values[index], recorded[index]);
            origins.record_computation(computations[index], recorded[index + 2_usize]);
            origins.record_value_type(value_types[index], recorded[index + 4_usize]);
            origins.record_comp_type(comp_types[index], recorded[index + 6_usize]);
        }
        let nodes = [
            CoreNode::Term(TermNode::Value(values[0_usize])),
            CoreNode::Term(TermNode::Value(values[1_usize])),
            CoreNode::Term(TermNode::Computation(computations[0_usize])),
            CoreNode::Term(TermNode::Computation(computations[1_usize])),
            CoreNode::Type(TypeNode::Value(value_types[0_usize])),
            CoreNode::Type(TypeNode::Value(value_types[1_usize])),
            CoreNode::Type(TypeNode::Computation(comp_types[0_usize])),
            CoreNode::Type(TypeNode::Computation(comp_types[1_usize])),
        ];
        let declaration = ByteSpan::new(ByteOffset::from(90_usize), ByteOffset::from(99_usize))
            .expect("the declaration is distinct from every node");
        for (node, span) in nodes.into_iter().zip(spans) {
            let refusal = Refusal::Checking(CheckRefusal::DanglingNode { node });
            let found = Annotations::refusal(refusal, declaration, &origins);
            assert_eq!(
                found.primary,
                Maybe::Present(Annotation {
                    span,
                    label: Label::Culprit(Culprit::of(refusal)),
                })
            );
            assert_eq!(found.context, UNNAMED);
        }
        let missing_value = arena.value_unit();
        let missing_computation = arena.computation_return(missing_value);
        let missing_type = arena.value_type_unit();
        let missing_comp_type = arena.comp_type_returner(missing_type);
        for node in [
            CoreNode::Term(TermNode::Value(missing_value)),
            CoreNode::Term(TermNode::Computation(missing_computation)),
            CoreNode::Type(TypeNode::Value(missing_type)),
            CoreNode::Type(TypeNode::Computation(missing_comp_type)),
        ] {
            let found = Annotations::refusal(
                Refusal::Checking(CheckRefusal::DanglingNode { node }),
                declaration,
                &origins,
            );
            assert_eq!(
                found.primary,
                Maybe::Absent(report_span::Absent::Unrecorded)
            );
            assert_eq!(found.context, UNNAMED);
        }
    }

    #[test]
    fn checker_fallbacks_preserve_causal_roles()
    {
        let spans: [ByteSpan; 4_usize] = core::array::from_fn(|index| {
            ByteSpan::new(
                ByteOffset::from(index * 10_usize),
                ByteOffset::from(index * 10_usize + 5_usize),
            )
            .expect("ordered fixture spans")
        });
        let recorded: [Origin; 3_usize] =
            core::array::from_fn(|index| Origin::new(NodeIndex::from(index), spans[index]));
        let mut arena = CoreArena::new();
        let value = arena.value_unit();
        let computation = arena.computation_return(value);
        let value_type = arena.value_type_unit();
        let expected = arena.comp_type_returner(value_type);
        let synthesised = arena.comp_type_returner(value_type);
        let mut origins = OriginTable::new();
        origins.record_computation(computation, recorded[0_usize]);
        origins.record_comp_type(expected, recorded[1_usize]);
        origins.record_comp_type(synthesised, recorded[2_usize]);
        let refusal = Refusal::Checking(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at: computation,
            expected,
            synthesised,
        }));
        let found = Annotations::refusal(refusal, spans[3_usize], &origins);
        assert_eq!(
            found.primary,
            Maybe::Present(Annotation {
                span: spans[0_usize],
                label: Label::Culprit(Culprit::of(refusal)),
            })
        );
        assert_eq!(found.context, [
            Maybe::Present(Annotation {
                span: spans[1_usize],
                label: Label::Expected
            }),
            Maybe::Present(Annotation {
                span: spans[2_usize],
                label: Label::Synthesised
            }),
        ]);
        let dependent = Annotations::refusal(
            Refusal::Checking(CheckRefusal::DependentBind {
                at: computation,
                synthesised,
            }),
            spans[3_usize],
            &origins,
        );
        assert_eq!(dependent.context, [
            Maybe::Present(Annotation {
                span: spans[2_usize],
                label: Label::Synthesised
            }),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]);
        let shape = Annotations::refusal(
            Refusal::Checking(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(computation),
                wanted: ExpectedShape::Arrow,
                found: TypeNode::Computation(synthesised),
            }),
            spans[3_usize],
            &origins,
        );
        assert_eq!(shape.context, [
            Maybe::Present(Annotation {
                span: spans[2_usize],
                label: Label::Met(ExpectedShape::Arrow)
            }),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]);
        for checking in [
            CheckRefusal::MachineInvariant,
            CheckRefusal::AdmissionOrder {
                constant: 3_usize.into(),
                admitted: 7_usize.into(),
            },
        ] {
            let refusal = Refusal::Checking(checking);
            let found = Annotations::refusal(refusal, spans[3_usize], &origins);
            assert_eq!(
                found.primary,
                Maybe::Present(Annotation {
                    span: spans[3_usize],
                    label: Label::Culprit(Culprit::of(refusal)),
                })
            );
            assert_eq!(found.context, UNNAMED);
        }
    }

    #[test]
    fn a_malformed_expectation_points_at_its_attribute()
    {
        let span = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
                .expect("ordered fixture spans")
        };
        let declaration = span(0_usize, 40_usize);
        let first = span(2_usize, 9_usize);
        let second = span(12_usize, 20_usize);
        let label = Label::Unsettled(Unsettlement::Malformed);
        let conflicting = Annotations::malformed(
            &Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }),
            declaration,
        );
        assert_eq!(
            conflicting.primary,
            Maybe::Present(Annotation {
                span: second,
                label
            }),
            "the contradicting attribute is the locus"
        );
        assert_eq!(
            conflicting.context,
            [
                Maybe::Present(Annotation {
                    span: first,
                    label: Label::First
                }),
                Maybe::Absent(report_context::Absent::Unnamed),
            ],
            "the attribute it contradicts is its context"
        );
        let negative = Annotations::malformed(
            &Stated::Malformed(ExpectationFault::NegativeObligations { span: first }),
            declaration,
        );
        assert_eq!(
            negative.primary,
            Maybe::Present(Annotation { span: first, label }),
            "a payload fault points at its attribute, not the declaration"
        );
        assert_eq!(negative.context, UNNAMED);
    }

    #[test]
    fn run_refusals_have_no_invented_source_locus()
    {
        let refusal = LoweringRefusal::BudgetExceeded {
            budget: 0_usize.into(),
        };
        let found = Annotations::lowering(refusal);
        assert_eq!(found.primary, Maybe::Absent(report_span::Absent::Run));
        assert_eq!(found.context, UNNAMED);
    }

    #[test]
    fn former_titles_distinguish_subjects_not_node_addresses()
    {
        let mut arena = CoreArena::new();
        let first = arena.value_unit();
        let second = arena.value_unit();
        assert_ne!(first, second, "the address-change fixture is non-vacuous");
        let formers = [
            UnadmittedFormer::ValueLift,
            UnadmittedFormer::NumericLiteral,
            UnadmittedFormer::NumericAtom,
            UnadmittedFormer::TypeLift,
            UnadmittedFormer::Abstract,
            UnadmittedFormer::SortParameter,
            UnadmittedFormer::TopUniverse,
            UnadmittedFormer::StaticLambda,
        ];
        let titles = formers.map(|former| {
            Checked(CheckRefusal::OutOfFragment {
                at: CoreNode::Term(TermNode::Value(first)),
                former,
            })
            .to_string()
        });
        for (index, former) in formers.into_iter().enumerate() {
            let changed = Checked(CheckRefusal::OutOfFragment {
                at: CoreNode::Term(TermNode::Value(second)),
                former,
            })
            .to_string();
            assert_eq!(
                titles[index], changed,
                "node addresses do not change a subject"
            );
            for earlier in &titles[.. index] {
                assert_ne!(
                    earlier, &titles[index],
                    "distinct formers remain distinguishable"
                );
            }
        }
    }

    #[test]
    fn checker_titles_preserve_numeric_roles()
    {
        let mut arena = CoreArena::new();
        let at = arena.value_unit();
        for (checking, expected) in [
            (
                CheckRefusal::UnknownConstant {
                    at,
                    constant: 3_usize.into(),
                },
                &[3_usize][..],
            ),
            (
                CheckRefusal::AdmissionOrder {
                    constant: 7_usize.into(),
                    admitted: 11_usize.into(),
                },
                &[7_usize, 11_usize][..],
            ),
            (
                CheckRefusal::FamilyArity {
                    at,
                    expected: 2_u32.into(),
                    actual: 5_u32.into(),
                },
                &[2_usize, 5_usize][..],
            ),
        ] {
            let title = Checked(checking).to_string();
            assert!(
                title
                    .split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq(expected.iter().copied()),
                "semantic payload order, without node ids: {title}"
            );
        }
    }

    #[test]
    fn recursion_titles_name_their_site_and_rule()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let field = OccurrenceSite::Field {
            tag: ConstructorTag::from(3_usize),
            field: FieldPosition::from(5_usize),
        };
        let parameter = OccurrenceSite::Parameter(ParameterPosition::from(2_usize));
        let titles: Vec<String> = [
            CheckRefusal::NegativeOccurrence(field),
            CheckRefusal::NestedOccurrence(field),
            CheckRefusal::IndexOccurrence(parameter),
            CheckRefusal::NonUniformOccurrence(field),
            CheckRefusal::CrossBlockReference {
                site: field,
                index: 9_usize.into(),
            },
            CheckRefusal::DescentNotReplayed {
                at: returned,
                reason: DescentRefusal::NotOverData,
            },
            CheckRefusal::DescentNotReplayed {
                at: returned,
                reason: DescentRefusal::NotCaseOnArgument,
            },
            CheckRefusal::DescentNotReplayed {
                at: returned,
                reason: DescentRefusal::BranchNotOverFields,
            },
            CheckRefusal::DescentNotReplayed {
                at: returned,
                reason: DescentRefusal::UnguardedSelfReference,
            },
            CheckRefusal::DescentNotReplayed {
                at: returned,
                reason: DescentRefusal::NonDescendingCall,
            },
        ]
        .map(|refusal| Checked(refusal).to_string())
        .into();
        for (index, title) in titles.iter().enumerate() {
            for earlier in &titles[.. index] {
                assert_ne!(earlier, title, "each subject stays distinguishable");
            }
        }
        let ordinals = |title: &str| -> Vec<usize> {
            title
                .split(|character: char| !character.is_ascii_digit())
                .filter_map(|digits| digits.parse::<usize>().ok())
                .collect()
        };
        assert_eq!(ordinals(&titles[0]), [5_usize, 3_usize], "field, then tag");
        assert_eq!(ordinals(&titles[2]), [2_usize], "the parameter");
        assert_eq!(
            ordinals(&titles[4]),
            [5_usize, 3_usize, 9_usize],
            "the site, then the later declaration"
        );
        assert!(ordinals(&titles[5]).is_empty(), "no node id: {}", titles[5]);
    }
}
