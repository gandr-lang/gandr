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
//! # The rules a refusal stood inside are contexts, not loci
//!
//! The judgements a checker refusal stood inside are its failure's
//! obligations, which the `frame` module reads into contexts. The loci here
//! are the ones the refusal itself names: the term refused, and the types it
//! compares where they were written.
//!
//! # Context is causal
//!
//! A report marks a second locus only when it is part of the cause: the earlier
//! signature a duplicate repeats, the type a term is checked against, the type
//! a term synthesises, the expected shape a former meets. Padding a snippet
//! with every nearby node would make the cause harder to find, not easier. A
//! context locus keeps its own span and its own label.

use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::CoreNode;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Mismatch;
use gandr_core_checker::RunFault;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::compared;
use gandr_core_checker::session::Capture;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_term::effect::Purity;
use gandr_core_term::session::ActionKind;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::Standing;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::ExpectationFault;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::Surviving;
use gandr_surface_lowering::Exit;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::culprit::Culprit;
use crate::report::Unsettlement;
use crate::report::report_span;
use crate::spelled::Spellings;
use crate::spelled::spelling;

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
    /// An endpoint of the path type a reflexivity was checked against.
    Endpoint,
    /// A declared name or a binder over a builtin: the primary locus of a
    /// shadowing warning.
    Shadows,
    /// A tail the source wrote without its exit: the primary locus of an
    /// `explicit-exits` finding, naming the exit inferred there.
    Inferred(Exit),
    /// A computation the source wrote where a value is read, which the
    /// checker runs: the primary locus of an `explicit-runs` finding, saying
    /// whether the run performs an effect.
    Ran(Purity),
    /// The declaration or refusal a ledger line reports.
    Reported,
    /// The fork that opened the endpoint a session refusal names.
    Forked,
    /// The first arm of an offer, which a later arm disagrees with.
    FirstArm,
    /// The earlier rule of a pair that rewrites one term apart, or whose
    /// joining the step budget left undecided.
    Overlaps,
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
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Culprit(culprit) => fmt::Display::fmt(&culprit, f),
            Self::Unsettled(unsettlement) => fmt::Display::fmt(&unsettlement, f),
            Self::Surviving(surviving) => write!(f, "surviving obligations: {surviving}"),
            Self::First => f.write_str("first written here"),
            Self::Declared => f.write_str("declared here"),
            Self::Expected => f.write_str("the type it is checked against"),
            Self::Synthesised => f.write_str("the type it synthesises"),
            Self::Met(wanted) => write!(f, "the type met, where {} is required", Shape(wanted)),
            Self::Endpoint => f.write_str("an endpoint the point does not convert to"),
            Self::Shadows => f.write_str("shadows a builtin"),
            Self::Inferred(exit) => write!(f, "exits by an inferred `{exit}`"),
            Self::Ran(Purity::Pure) => f.write_str("runs by an inferred `run`"),
            Self::Ran(Purity::Effectful) => {
                f.write_str("runs by an inferred `run`, performing an effect")
            },
            Self::Reported => f.write_str("reported here"),
            Self::Forked => f.write_str("the endpoint was opened by this fork"),
            Self::FirstArm => f.write_str("the arm it disagrees with"),
            Self::Overlaps => f.write_str("the rule it overlaps"),
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
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
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
            Maybe::Present(node) => spellings.get(node).map(AsRef::as_ref),
            Maybe::Absent(_) => Maybe::Absent(spelling::Absent::Unspelled),
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
            (Maybe::Present(expected), Maybe::Present(found)) => {
                write!(f, "expected `{expected}`, found `{found}`")
            },
            (Maybe::Present(expected), Maybe::Absent(_)) => write!(f, "expected `{expected}`"),
            (Maybe::Absent(_), Maybe::Present(found)) => write!(f, "found `{found}`"),
            (Maybe::Absent(_), Maybe::Absent(_)) => Ok(()),
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
            | ExpectationFault::ObligationsBeyondRange { span }
            | ExpectationFault::UnwrittenNormalForm { span }) =>
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
            Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }) => {
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
            Stated::Malformed(
                ExpectationFault::UnknownRefusal { span }
                | ExpectationFault::NegativeObligations { span }
                | ExpectationFault::ObligationsBeyondRange { span }
                | ExpectationFault::UnwrittenNormalForm { span },
            ) => Self::at(span, label),
            Stated::Verdict(_) => Self::at(declaration, label),
        }
    }

    /// The loci of a lowering refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the primary locus is the span the lowering rejected, labelled
    ///   with what those bytes are, and is absent for the two refusals about
    ///   the run rather than a position; a duplicate declaration, import alias
    ///   or attribute marks its first occurrence as context, a member named
    ///   before its declaration marks that declaration, and a pair of rules
    ///   that part, or whose joining went undecided, marks the earlier rule.
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
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_is_located`
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
                LoweringRefusal::RulesDiverge { first, .. } | LoweringRefusal::RulesUndecided { first, .. } =>
                    ret.context[0_usize] == Maybe::Present(Annotation { span: first, label: Label::Overlaps }),
                LoweringRefusal::UnresolvedName { .. } | LoweringRefusal::UnresolvedDocLink { .. } | LoweringRefusal::UnresolvedTypeHead { .. } | LoweringRefusal::ShadowedBuiltin { .. } | LoweringRefusal::OutOfFragment { .. } | LoweringRefusal::GradedBridge { .. } | LoweringRefusal::MalformedLiteral { .. } | LoweringRefusal::MalformedForm { .. } | LoweringRefusal::UnknownAttribute { .. } | LoweringRefusal::MissingPayload { .. } | LoweringRefusal::NonValuePayload { .. } | LoweringRefusal::IllTypedPayload { .. } | LoweringRefusal::UnknownMember { .. } | LoweringRefusal::NotAFunctor { .. } | LoweringRefusal::ProjectionFromApplication { .. } | LoweringRefusal::UnreadAscription { .. } | LoweringRefusal::UnstatedComponent { .. } | LoweringRefusal::FamilyTelescope { .. } | LoweringRefusal::LowercaseModuleName { .. } | LoweringRefusal::NonExhaustiveMatch { .. } | LoweringRefusal::UnmarkedSelfReference { .. } | LoweringRefusal::Unreachable { .. } | LoweringRefusal::OutsideLoop { .. } | LoweringRefusal::AcrossHandler { .. } | LoweringRefusal::ForNeedsListCase { .. } | LoweringRefusal::WithoutK { .. } | LoweringRefusal::DirectedCell { .. } | LoweringRefusal::CellNotALoop { .. } | LoweringRefusal::RulesUnoriented { .. } | LoweringRefusal::BudgetExceeded { .. } | LoweringRefusal::GrammarMismatch { .. } | LoweringRefusal::UnknownMold { .. } => ret.context[0_usize] == Maybe::Absent(report_context::Absent::Unnamed),
            }
    })]
    pub fn lowering(refusal: LoweringRefusal<'_>) -> Self
    {
        let primary = match refusal.span() {
            Maybe::Present(span) => Maybe::Present(Annotation {
                span,
                label: Label::Culprit(Culprit::of(Refusal::Lowering(refusal))),
            }),
            Maybe::Absent(_) => Maybe::Absent(report_span::Absent::Run),
        };
        let context = match refusal {
            LoweringRefusal::DuplicateSignature { first, .. }
            | LoweringRefusal::DuplicateDefinition { first, .. }
            | LoweringRefusal::DuplicateImportAlias { first, .. }
            | LoweringRefusal::DuplicateAttribute { first, .. } => Maybe::Present(Annotation {
                span: first,
                label: Label::First,
            }),
            LoweringRefusal::ForwardMemberReference { declared, .. } => {
                Maybe::Present(Annotation {
                    span: declared,
                    label: Label::Declared,
                })
            },
            LoweringRefusal::RulesDiverge { first, .. }
            | LoweringRefusal::RulesUndecided { first, .. } => Maybe::Present(Annotation {
                span: first,
                label: Label::Overlaps,
            }),
            LoweringRefusal::UnresolvedName { .. }
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
            | LoweringRefusal::NotAFunctor { .. }
            | LoweringRefusal::ProjectionFromApplication { .. }
            | LoweringRefusal::UnreadAscription { .. }
            | LoweringRefusal::UnstatedComponent { .. }
            | LoweringRefusal::FamilyTelescope { .. }
            | LoweringRefusal::LowercaseModuleName { .. }
            | LoweringRefusal::NonExhaustiveMatch { .. }
            | LoweringRefusal::UnmarkedSelfReference { .. }
            | LoweringRefusal::Unreachable { .. }
            | LoweringRefusal::OutsideLoop { .. }
            | LoweringRefusal::AcrossHandler { .. }
            | LoweringRefusal::ForNeedsListCase { .. }
            | LoweringRefusal::WithoutK { .. }
            | LoweringRefusal::DirectedCell { .. }
            | LoweringRefusal::CellNotALoop { .. }
            | LoweringRefusal::RulesUnoriented { .. }
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
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_is_located`
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
    #[spec(ensures: |ref ret| {
        let label = Label::Culprit(Culprit::of(refusal));
        let labelled = match ret.primary {
            Maybe::Present(annotation) => annotation.label == label,
            Maybe::Absent(report_span::Absent::Run | report_span::Absent::Unrecorded) => true,
            Maybe::Absent(report_span::Absent::OutsideText | report_span::Absent::Standing) => false,
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
            Refusal::Lowering(lowering) => Self::lowering(lowering),
            Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { span, .. }) => {
                Self::at(span, Label::Culprit(Culprit::of(refusal)))
            },
            Refusal::Checking(checking) => checked(checking, declaration, origins),
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
///   order; selected whole-declaration failures expose fallback precedence; a
///   session mismatch and disagreeing offer arms expose the fork and the first
///   arm. Other checker constructors are not individually enumerated.
/// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
/// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
/// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
/// - witness: `locus::tests::checker_fallbacks_preserve_causal_roles`
/// - witness: `locus::tests::session_refusals_point_at_the_fork_and_name_the_action`
#[spec(ensures: |ref ret| {
    let label = Label::Culprit(Culprit::of(Refusal::Checking(refusal)));
    let labelled = match ret.primary {
        Maybe::Present(annotation) => annotation.label == label,
        Maybe::Absent(report_span::Absent::Unrecorded) => true,
        Maybe::Absent(report_span::Absent::Run | report_span::Absent::OutsideText | report_span::Absent::Standing) => false,
    };
    let role = |slot: &Maybe<Annotation, report_context::Absent>, wanted| match *slot {
        Maybe::Present(annotation) => annotation.label == wanted,
        Maybe::Absent(report_context::Absent::Unrecorded) => true,
        Maybe::Absent(report_context::Absent::Unnamed | report_context::Absent::OutsideText) => false,
    };
    labelled && match refusal {
        CheckRefusal::DataFieldLevel {..} | CheckRefusal::MissingRecordField {..} => role(&ret.context[0_usize],Label::Expected) && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::TypeMismatch(_) | CheckRefusal::SortMismatch { .. }
            | CheckRefusal::LevelMismatch { .. } | CheckRefusal::FamilyArgumentClassifier { .. }
            | CheckRefusal::NotOver { .. } =>
            role(&ret.context[0_usize], Label::Expected) && role(&ret.context[1_usize], Label::Synthesised),
        CheckRefusal::DependentBind { .. } | CheckRefusal::CompoundEndpoint { .. } | CheckRefusal::FunextUnsupported { .. }
            | CheckRefusal::EquivUnsupported { .. } | CheckRefusal::UncertifiedStratum { .. } => role(&ret.context[0_usize], Label::Synthesised)
            && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::ShapeMismatch { wanted, .. } => role(&ret.context[0_usize], Label::Met(wanted))
            && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::EndpointMismatch { .. } => role(&ret.context[0_usize], Label::Endpoint)
            && role(&ret.context[1_usize], Label::Endpoint),
        CheckRefusal::SessionMismatch { .. }
            | CheckRefusal::Linearity { defect: LinearityDefect::Residue { .. } | LinearityDefect::Closed { .. }
                | LinearityDefect::UsedTwice { .. } | LinearityDefect::Captured { .. } | LinearityDefect::AsValue { .. }, .. } =>
            role(&ret.context[0_usize], Label::Forked) && ret.context[1_usize] == Maybe::Absent(report_context::Absent::Unnamed),
        CheckRefusal::Linearity { defect: LinearityDefect::ArmsDisagree { .. }, .. } =>
            role(&ret.context[0_usize], Label::Forked) && role(&ret.context[1_usize], Label::FirstArm),
        CheckRefusal::NotSynthesisable { form: CheckingForm::Hole(_) }
            | CheckRefusal::NotADataType(_) | CheckRefusal::NotAnAbstractType(_)
            | CheckRefusal::SealSiteRepeated(_)
            | CheckRefusal::NegativeOccurrence(_) | CheckRefusal::NestedOccurrence(_)
            | CheckRefusal::IndexOccurrence(_) | CheckRefusal::NonUniformOccurrence(_)
            | CheckRefusal::CrossBlockReference { .. }
            | CheckRefusal::BudgetExceeded { .. } | CheckRefusal::AdmissionOrder { .. }
            | CheckRefusal::MachineInvariant | CheckRefusal::CapabilityUngranted { .. } => ret.primary == Maybe::Present(Annotation {
                span: declaration, label,
            }) && ret.context == UNNAMED,
        CheckRefusal::DataKindNotUniverse(_) | CheckRefusal::RuleNotPresentable { .. } | CheckRefusal::RuleNotRespected { .. } | CheckRefusal::NotApart { .. } | CheckRefusal::LoopNotRespected { .. } | CheckRefusal::AbstractKindNotUniverse(_) | CheckRefusal::RepresentationAboveKind { .. } | CheckRefusal::DataArgumentArity(_) | CheckRefusal::UnknownConstructor { .. } | CheckRefusal::ConstructorArity(_) | CheckRefusal::NonExhaustiveDataCase(_) | CheckRefusal::AbsentRecordField(_) | CheckRefusal::AbsentTupleComponent(_) | CheckRefusal::UnknownOperation { .. } | CheckRefusal::HandlerCoverage { .. } | CheckRefusal::ShiftWithoutReset { .. } | CheckRefusal::DependentStack { .. } | CheckRefusal::PathCode(_) | CheckRefusal::PointwiseDistinct { .. } | CheckRefusal::RoundTripDistinct { .. } | CheckRefusal::UaUncertified { .. } | CheckRefusal::UaInequivalent { .. } | CheckRefusal::EffectSignatureConflict { .. } | CheckRefusal::NotSynthesisable { .. } | CheckRefusal::UnknownConstant { .. } | CheckRefusal::OutOfFragment { .. } | CheckRefusal::UnboundIndex { .. } | CheckRefusal::DanglingNode { .. } | CheckRefusal::Undecided { .. } | CheckRefusal::FamilyArity { .. } | CheckRefusal::StaticLambdaArgument { .. } | CheckRefusal::StaticClassifierExpected { .. } | CheckRefusal::StageNotBelow { .. } | CheckRefusal::Linearity { .. } | CheckRefusal::UnenclosedRun { .. } | CheckRefusal::CapabilityForged { .. } | CheckRefusal::CapabilityAmplified(_) | CheckRefusal::CapabilityOutsideAuthority { .. } | CheckRefusal::CapabilityEscaped { .. } | CheckRefusal::CapabilityConsumable(_) | CheckRefusal::SessionNotEquivalent { .. } | CheckRefusal::SessionNotSubtype { .. } | CheckRefusal::SessionCodeExpected { .. } | CheckRefusal::NonCovariantMotive { .. } | CheckRefusal::RideUnsupported { .. } | CheckRefusal::RunNotAdmitted { .. } | CheckRefusal::ForwardUnsupported { .. } | CheckRefusal::Boundary { .. } | CheckRefusal::Access { .. } => ret.context == UNNAMED,
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
        CheckRefusal::DataKindNotUniverse(at)
        | CheckRefusal::DataArgumentArity(at)
        | CheckRefusal::AbstractKindNotUniverse(at)
        | CheckRefusal::CapabilityConsumable(at)
        | CheckRefusal::RuleNotPresentable { kind: at, .. } => {
            (spanned(origins.value_type(at)), UNNAMED)
        },
        CheckRefusal::DataFieldLevel { field: at, kind }
        | CheckRefusal::RepresentationAboveKind {
            representation: at,
            kind,
        } => (spanned(origins.value_type(at)), [
            annotated(spanned(origins.value_type(kind)), Label::Expected),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::UnknownConstructor { at, .. } | CheckRefusal::ConstructorArity(at) => {
            (spanned(origins.value(at)), UNNAMED)
        },
        CheckRefusal::MissingRecordField { at, expected }
        | CheckRefusal::CapabilityForged { at, expected } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value_type(expected)), Label::Expected),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::DependentStack { at, synthesised }
        | CheckRefusal::CompoundEndpoint { at, synthesised } => (spanned(origins.value(at)), [
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::EndpointMismatch { at, left, right } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value(left)), Label::Endpoint),
            annotated(spanned(origins.value(right)), Label::Endpoint),
        ]),
        CheckRefusal::FunextUnsupported { at, classifier }
        | CheckRefusal::EquivUnsupported { at, classifier }
        | CheckRefusal::UncertifiedStratum {
            at,
            code: classifier,
        } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value_type(classifier)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::EffectSignatureConflict { at, .. } => {
            (spanned(origins.computation(at)), UNNAMED)
        },
        CheckRefusal::TypeMismatch(Mismatch::Value {
            at,
            synthesised,
            expected,
        })
        | CheckRefusal::CapabilityAmplified(Mismatch::Value {
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
        }
        | CheckRefusal::NotOver {
            at,
            synthesised,
            expected,
        } => (spanned(origins.value(at)), [
            annotated(spanned(origins.value_type(expected)), Label::Expected),
            annotated(spanned(origins.value_type(synthesised)), Label::Synthesised),
        ]),
        CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected,
        })
        | CheckRefusal::CapabilityAmplified(Mismatch::Computation {
            at,
            synthesised,
            expected,
        }) => (spanned(origins.computation(at)), [
            annotated(spanned(origins.comp_type(expected)), Label::Expected),
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
        ]),
        CheckRefusal::DependentBind { at, synthesised } => (spanned(origins.computation(at)), [
            annotated(spanned(origins.comp_type(synthesised)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::ShapeMismatch { at, wanted, found } => (node(origins, CoreNode::Term(at)), [
            annotated(node(origins, CoreNode::Type(found)), Label::Met(wanted)),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::NotSynthesisable {
            form:
                CheckingForm::Reify(at)
                | CheckingForm::List(at)
                | CheckingForm::Injection(at)
                | CheckingForm::Thunk(at)
                | CheckingForm::StaticLambda(at)
                | CheckingForm::Nested(at)
                | CheckingForm::Run(at),
        }
        | CheckRefusal::PathCode(at)
        | CheckRefusal::UnknownConstant { at, .. }
        | CheckRefusal::UnboundIndex { at, .. }
        | CheckRefusal::Undecided { at }
        | CheckRefusal::FamilyArity { at, .. }
        | CheckRefusal::StaticLambdaArgument { at }
        | CheckRefusal::PointwiseDistinct { at }
        | CheckRefusal::RoundTripDistinct { at }
        | CheckRefusal::UaUncertified { at, .. }
        | CheckRefusal::UaInequivalent { at, .. }
        | CheckRefusal::UnenclosedRun { at }
        | CheckRefusal::SessionNotEquivalent { at }
        | CheckRefusal::SessionNotSubtype { at }
        | CheckRefusal::SessionCodeExpected { at }
        | CheckRefusal::RunNotAdmitted { at, .. }
        | CheckRefusal::ForwardUnsupported { at }
        | CheckRefusal::StageNotBelow { at, .. }
        | CheckRefusal::Boundary { at } => (spanned(origins.value(at)), UNNAMED),
        CheckRefusal::StaticClassifierExpected { found, .. } => {
            (spanned(origins.value_type(found)), UNNAMED)
        },
        CheckRefusal::CapabilityEscaped { at, found } => (node(origins, CoreNode::Term(at)), [
            annotated(node(origins, CoreNode::Type(found)), Label::Synthesised),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::UnknownOperation { at }
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
                | CheckingForm::Fixpoint(at)
                | CheckingForm::Offer(at)
                | CheckingForm::Scope(at),
        }
        | CheckRefusal::CapabilityOutsideAuthority { at, .. }
        | CheckRefusal::NonExhaustiveDataCase(at)
        | CheckRefusal::RuleNotRespected { at, .. }
        | CheckRefusal::NotApart { at, .. }
        | CheckRefusal::LoopNotRespected { at, .. }
        | CheckRefusal::AbsentRecordField(at)
        | CheckRefusal::AbsentTupleComponent(at)
        | CheckRefusal::NonCovariantMotive { at }
        | CheckRefusal::RideUnsupported { at } => (spanned(origins.computation(at)), UNNAMED),
        CheckRefusal::OutOfFragment { at: core, .. }
        | CheckRefusal::DanglingNode { node: core } => (node(origins, core), UNNAMED),
        CheckRefusal::NotADataType(_)
        | CheckRefusal::NotAnAbstractType(_)
        | CheckRefusal::SealSiteRepeated(_)
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
        | CheckRefusal::MachineInvariant
        | CheckRefusal::CapabilityUngranted { .. } => return Annotations::at(declaration, label),
        CheckRefusal::SessionMismatch { at, endpoint, .. } => (spanned(origins.computation(at)), [
            annotated(spanned(origins.computation(endpoint.fork)), Label::Forked),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::Linearity {
            at,
            defect:
                LinearityDefect::ArmsDisagree {
                    endpoint, first, ..
                },
        } => (node(origins, at), [
            annotated(spanned(origins.computation(endpoint.fork)), Label::Forked),
            annotated(spanned(origins.computation(first)), Label::FirstArm),
        ]),
        CheckRefusal::Linearity {
            at,
            defect:
                LinearityDefect::Residue { endpoint, .. }
                | LinearityDefect::Closed { endpoint }
                | LinearityDefect::UsedTwice { endpoint }
                | LinearityDefect::Captured { endpoint, .. }
                | LinearityDefect::AsValue { endpoint },
        } => (node(origins, at), [
            annotated(spanned(origins.computation(endpoint.fork)), Label::Forked),
            Maybe::Absent(report_context::Absent::Unnamed),
        ]),
        CheckRefusal::Linearity {
            at,
            defect:
                LinearityDefect::Delegated
                | LinearityDefect::Unrestricted
                | LinearityDefect::Unbound { .. },
        }
        | CheckRefusal::Access { at, .. } => (node(origins, at), UNNAMED),
    };
    let primary = match primary {
        Maybe::Present(span) => Maybe::Present(Annotation { span, label }),
        Maybe::Absent(node_span::Absent::Unrecorded) => {
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
        Maybe::Present(origin) => Maybe::Present(origin.span()),
        Maybe::Absent(_) => Maybe::Absent(node_span::Absent::Unrecorded),
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
pub fn node(
    origins: &OriginTable,
    core: CoreNode,
) -> Maybe<ByteSpan, node_span::Absent>
{
    match core {
        CoreNode::Term(TermNode::Value(at)) => spanned(origins.value(at)),
        CoreNode::Term(TermNode::Computation(at)) => spanned(origins.computation(at)),
        CoreNode::Type(TypeNode::Value(at)) => spanned(origins.value_type(at)),
        CoreNode::Type(TypeNode::Computation(at)) => spanned(origins.comp_type(at)),
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
        Maybe::Present(span) => Maybe::Present(Annotation { span, label }),
        Maybe::Absent(node_span::Absent::Unrecorded) => {
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
    /// - witness: `locus::tests::session_refusals_point_at_the_fork_and_name_the_action`
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
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
            CheckRefusal::RuleNotPresentable { refusal, .. } => write!(f, "rule {} does not present its datatype: {}", usize::from(refusal.rule), match refusal.fault {
                gandr_kernel_term::RuleFault::VariableHeaded => "its left side is a bare variable",
                gandr_kernel_term::RuleFault::UnknownConstructor => "it names a constructor the datatype does not declare",
                gandr_kernel_term::RuleFault::Arity => "a constructor in it has the wrong number of fields",
                gandr_kernel_term::RuleFault::NotOwnPosition => "a constructor in it stands at a field of another type",
                gandr_kernel_term::RuleFault::NonLinear => "its left side repeats or skips a variable",
                gandr_kernel_term::RuleFault::Unbound => "its right side names a variable the left side does not bind",
                gandr_kernel_term::RuleFault::Duplicated => "its right side names a variable twice",
                gandr_kernel_term::RuleFault::SlotMismatch => "its right side moves a variable to a field of another type",
                gandr_kernel_term::RuleFault::NotDecreasing => "its right side is not smaller than its left",
            }),
            CheckRefusal::RuleNotRespected { rule, .. } => write!(f, "the case is not shown to respect rule {} of its datatype", usize::from(rule)),
            CheckRefusal::NotApart { reason, .. } => match reason {
                gandr_kernel_term::Apartness::Apart => f.write_str("the path's endpoints are apart"),
                gandr_kernel_term::Apartness::Agree => f.write_str("the path's endpoints have one normal form"),
                gandr_kernel_term::Apartness::Open => f.write_str("an endpoint holds a subterm of its datatype that is no constructor"),
                gandr_kernel_term::Apartness::Leaf => f.write_str("the endpoints differ only at a subterm of another type"),
                gandr_kernel_term::Apartness::Diverges { outer, inner } => write!(f, "rules {} and {} of the datatype do not converge", usize::from(outer), usize::from(inner)),
                gandr_kernel_term::Apartness::Undecided => f.write_str("the endpoints were not decided within the rewrite budget"),
            },
            CheckRefusal::LoopNotRespected { cell, .. } => write!(f, "the case is not shown to respect loop {} of its sort: carried along the loop, its answer at the loop's point does not convert with that answer", usize::from(cell)),
            CheckRefusal::AbstractKindNotUniverse(_) => f.write_str("an abstract type's kind must be a value universe"),
            CheckRefusal::RepresentationAboveKind {..} => f.write_str("a sealed representation exceeds its abstract type's universe"),
            CheckRefusal::NotAnAbstractType(constant) => write!(f,"declaration {} is not an abstract type",usize::from(constant)),
            CheckRefusal::SealSiteRepeated(site) => write!(f,"{site} was sealed twice"),
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
            | CheckRefusal::EndpointMismatch { .. } => f.write_str("reflexivity requires its point to convert to both endpoints of the path type"),
            | CheckRefusal::CompoundEndpoint { .. } => f.write_str("a compound endpoint must return a value without effects"),
            | CheckRefusal::FunextUnsupported { .. } => f.write_str("function extensionality is decided for closed pure functions with a finite first-order coverage, function arguments between first-order types included"),
            | CheckRefusal::PointwiseDistinct { .. } => f.write_str("function extensionality requires both functions to agree at every input, returning one value or applying their argument at one input"),
            | CheckRefusal::EquivUnsupported { .. } => f.write_str("a universe equivalence is decided for closed pure translators between finite first-order types"),
            | CheckRefusal::UncertifiedStratum { .. } => f.write_str("a universe equivalence over a recursive type has no finite coverage to certify its round trips"),
            | CheckRefusal::RoundTripDistinct { .. } => f.write_str("a universe equivalence requires each round trip to return its input at every pattern"),
            | CheckRefusal::NotOver { .. } => f.write_str("a telescope transport requires its second identity to lie over its path, from the start transported along it"),
            | CheckRefusal::UaUncertified { stratum, .. } => match stratum {
                | StratumDefect::Degree { degree } => write!(
                    f,
                    "univalence is certified from degree 1 to the largest degree of a shape in the catalogue, not degree {}",
                    usize::from(degree)
                ),
                | StratumDefect::Condition { degree } if usize::from(degree) == 1 => f.write_str(
                    "univalence needs a catalogue of size 1 or more, whose site satisfies the corolla condition",
                ),
                | StratumDefect::Condition { degree } => write!(
                    f,
                    "univalence above degree 1 needs every shape up to its degree to be the colimit of its corollas; a shape of degree {} is not",
                    usize::from(degree)
                ),
                | StratumDefect::Allowance { bound } => write!(
                    f,
                    "univalence enumerates catalogues of size up to 5, not {}",
                    usize::from(bound)
                ),
            },
            | CheckRefusal::UaInequivalent { defect, .. } => match defect {
                | UaDefect::UnknownGenerator { .. } => f.write_str(
                    "a translator record must be keyed by generators its description declares",
                ),
                | UaDefect::PastTheBound { profile } => write!(
                    f,
                    "a generator of {} inputs and {} outputs stands past the catalogue's bound",
                    usize::from(profile.inputs),
                    usize::from(profile.outputs)
                ),
                | UaDefect::Cardinality { .. } => {
                    f.write_str("the two species have different numbers of elements at a corolla")
                },
                | UaDefect::Tables { .. } => {
                    f.write_str("each corolla needs exactly one translator on each side")
                },
                | UaDefect::NotInverse { .. } => {
                    f.write_str("the backward translator does not return what the forward one sends")
                },
                | UaDefect::NotNatural { .. } => {
                    f.write_str("the translators do not commute with the corolla's symmetries")
                },
                | UaDefect::Stuck { .. } => {
                    f.write_str("a translator returns no element of its target code")
                },
            },
            | CheckRefusal::UnenclosedRun { .. } => f.write_str("a run where a value is read needs a computation around it to run before"),
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
                    | CheckingForm::Nested(_) => "a computation read as a value",
                    | CheckingForm::Offer(_) => "an offer",
                    | CheckingForm::Scope(_) => "a capability scope",
                    | CheckingForm::Run(_) => "a recorded run",
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
            | CheckRefusal::StageNotBelow { found, .. } => write!(
                f,
                "the value is not strictly below the parameter its structural recursion \
                 descends on: {}",
                Stood(found)
            ),
            | CheckRefusal::SessionMismatch { defect, .. } => match defect {
                | ProtocolDefect::Action { expected, observed } => write!(
                    f,
                    "the endpoint's session type admits {} here, not {}",
                    Action(expected),
                    Action(observed)
                ),
                | ProtocolDefect::Label => {
                    f.write_str("the label selected is not one the endpoint's session type offers")
                },
                | ProtocolDefect::Arms => f.write_str(
                    "an offer needs exactly one arm for each label its endpoint's session type offers",
                ),
            },
            | CheckRefusal::Linearity { defect, .. } => match defect {
                | LinearityDefect::Residue { .. } => f.write_str(
                    "a half of the fork finishes with an endpoint its session type has not closed",
                ),
                | LinearityDefect::Closed { .. } => f.write_str("the endpoint is used after it was closed"),
                | LinearityDefect::UsedTwice { .. } => {
                    f.write_str("one action names the endpoint twice")
                },
                | LinearityDefect::Captured { by, .. } => write!(
                    f,
                    "the endpoint is named inside {}, which may run its use other than once",
                    Captor(by)
                ),
                | LinearityDefect::Delegated => f.write_str(
                    "a payload is an endpoint or a session type: sending an endpoint is not admitted",
                ),
                | LinearityDefect::AsValue { .. } => {
                    f.write_str("the endpoint is read as a value outside a session action")
                },
                | LinearityDefect::ArmsDisagree { .. } => {
                    f.write_str("the arms of the offer leave the endpoints in different states")
                },
                | LinearityDefect::Unrestricted => f.write_str(
                    "the declaration's type is a session type: an endpoint exists only inside a fork",
                ),
                | LinearityDefect::Unbound { index } => write!(
                    f,
                    "the action names linear index {}, which no fork bound",
                    u32::from(index)
                ),
            },
            | CheckRefusal::Access { defect, .. } => match defect {
                | AccessDefect::NotHeld => f.write_str("the access names a linear slot that holds no value"),
                | AccessDefect::Lent => f.write_str("the held value is lent to an access and cannot be named here"),
                | AccessDefect::HeldCaptured { by } => write!(
                    f,
                    "the held value is named inside {}, which may run its holding other than once",
                    Captor(by)
                ),
                | AccessDefect::Escaped { by } => write!(
                    f,
                    "the view is named inside {}, which may outlive the access's body",
                    Captor(by)
                ),
                | AccessDefect::Unended => {
                    f.write_str("the access's body ends with its view neither resumed nor aborted")
                },
                | AccessDefect::Spent => f.write_str("the view is used after its resume or abort"),
                | AccessDefect::NotAView => f.write_str("the resume or abort names a linear slot that is no view"),
                | AccessDefect::UnwindEffect => f.write_str(
                    "the access's unwind performs an effect: an unwind runs under the empty row",
                ),
            },
            | CheckRefusal::CapabilityForged { .. } => f.write_str(
                "a capability type is inhabited only by a capability hypothesis, and this term \
                 is none",
            ),
            | CheckRefusal::CapabilityAmplified(_) => f.write_str(
                "this capability grants less than the capability it is checked against",
            ),
            | CheckRefusal::CapabilityOutsideAuthority { .. } => f.write_str(
                "the capability this operation is exercised through does not grant it",
            ),
            | CheckRefusal::CapabilityEscaped { .. } => f.write_str(
                "a capability a scope introduces would outlive the scope here",
            ),
            | CheckRefusal::CapabilityConsumable(_) => f.write_str(
                "a consumable capability belongs in the linear zone, which admits no binder",
            ),
            | CheckRefusal::CapabilityUngranted { constant, .. } => write!(
                f,
                "declaration {} holds a capability beyond the authority the host grants",
                usize::from(constant)
            ),
            | CheckRefusal::SessionNotEquivalent { .. } => f.write_str(
                "a session equivalence requires the two protocols to be bisimilar, payload by payload",
            ),
            | CheckRefusal::SessionNotSubtype { .. } => f.write_str(
                "a session simulation requires its source to select no more and offer no less than its target",
            ),
            | CheckRefusal::SessionCodeExpected { .. } => {
                f.write_str("a session identity relates quoted session types at their protocol's root")
            },
            | CheckRefusal::NonCovariantMotive { .. } => f.write_str(
                "a flow runs one way, so a ride's motive may use its moving endpoint only covariantly",
            ),
            | CheckRefusal::RideUnsupported { .. } => f.write_str(
                "a ride moves a constant motive, a run of the moving endpoint, a value whose type relates its two endpoints, or a decode of the moving code inside products, sums, lists and flows into it",
            ),
            | CheckRefusal::RunNotAdmitted { fault, .. } => match fault {
                | RunFault::WrongDirection(step) => write!(
                    f,
                    "move {} of the run goes the other way from the protocol's next action",
                    u32::from(step).saturating_add(1)
                ),
                | RunFault::WrongLabel(step) => write!(
                    f,
                    "move {} of the run takes a label the protocol does not admit there",
                    u32::from(step).saturating_add(1)
                ),
                | RunFault::ResumeAfterEnd(step) => write!(
                    f,
                    "move {} of the run follows the protocol's end",
                    u32::from(step).saturating_add(1)
                ),
                | RunFault::Incomplete(step) => write!(
                    f,
                    "the run stops after {} moves, before its protocol ends",
                    u32::from(step)
                ),
                | RunFault::OfferNarrowed => f.write_str(
                    "a run that is not a literal may take any offer its protocol makes, and the flow's target drops one",
                ),
            },
            | CheckRefusal::ForwardUnsupported { .. } => f.write_str(
                "a forward flow's translator is closed, maps between first-order codes, and sends every source leaf to a target position of its own type",
            ),
            | CheckRefusal::Boundary { .. } => f.write_str(
                "an arrow's domain flow runs from the target's argument to the source's, and its codomain flow from the source's result to the target's",
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
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            ExpectedShape::Data => "a nominal datatype",
            ExpectedShape::Record => "a record type",
            ExpectedShape::Stack => "a stack type from input to output computation",
            ExpectedShape::With => "a lazy pair of computation types",
            ExpectedShape::PathUniverse => "a universe-path classifier `Path_U a b`",
            ExpectedShape::Sum => "a sum type `A + B`",
            ExpectedShape::List => "a List type `List(A)`",
            ExpectedShape::Thunk => "a thunk type `+U C`",
            ExpectedShape::Returner => "a returner `-F A`",
            ExpectedShape::Arrow => "an arrow `A → C`",
            ExpectedShape::Product => "an eager product `A * B`",
            ExpectedShape::Sigma => "a dependent record `#{x : A, y : B(x)}`",
            ExpectedShape::StaticPi => "a type operator's classifier `K -> J`",
            ExpectedShape::Path => "an element path type `Path(A, a, b)`",
            ExpectedShape::Telescope => "a telescope motive `Π (y : A). Π (z : B). F C`",
            ExpectedShape::Session => {
                "a session type `!A. S`, `?A. S`, `+{l : S}`, `&{l : S}` or `end`"
            },
            ExpectedShape::Capability => "a capability `Cap {op, …}`",
            ExpectedShape::Flow => "a flow type `Flow(A, a, b)`",
            ExpectedShape::Run => "a run type `Run(s)`",
        })
    }
}

/// A session action, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Action(pub ActionKind);

impl fmt::Display for Action
{
    /// Writes the action with its article.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one noun phrase per action kind.
    /// - provides: both sides of a session mismatch's title.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send refused for a close titles the admitted action
    ///   before the attempted one, and swapping them changes the title; exact
    ///   wording and destination failures are outside this observation.
    /// - witness: `locus::tests::session_refusals_point_at_the_fork_and_name_the_action`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            ActionKind::Send => "a send",
            ActionKind::Receive => "a receive",
            ActionKind::Select => "a selection",
            ActionKind::Offer => "an offer",
            ActionKind::Close => "a close",
        })
    }
}

/// What may run an endpoint's use other than once, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Captor(pub Capture);

impl fmt::Display for Captor
{
    /// Writes the captor with its article.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one noun phrase per captor.
    /// - provides: the subject of a captured endpoint's title.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the five captors read as five distinct titles; exact
    ///   wording and destination failures are outside this observation.
    /// - witness: `locus::tests::session_refusals_point_at_the_fork_and_name_the_action`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            Capture::Thunk => "a thunk",
            Capture::Recursion => "a fixpoint",
            Capture::Branch => "a branch of a case, a lazy pair or a fold",
            Capture::Stack => "a first-class stack",
            Capture::Continuation => "a continuation a handler or a shift may resume",
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
            | UnadmittedFormer::ValueLift => "an explicit universe lift of a value",
            | UnadmittedFormer::NumericLiteral => "a numeric literal",

            | UnadmittedFormer::NumericAtom => "the numeric base atom",

            | UnadmittedFormer::TypeLift => "a lift of a value type to a level not above its own",
            | UnadmittedFormer::Abstract => "a sealed abstract type",
            | UnadmittedFormer::SortParameter => "a universe over a sort parameter",
            | UnadmittedFormer::TopUniverse => "a universe at the greatest representable level",
            | UnadmittedFormer::StaticLambda => "a type operator",
            | UnadmittedFormer::EffectRow => "a nonempty effect row at the pure kernel boundary",
            | UnadmittedFormer::Capability => "a capability type at the pure kernel boundary",
            | UnadmittedFormer::Exercise => "an exercised capability at the pure kernel boundary",
            | UnadmittedFormer::Scope => "a capability scope at the pure kernel boundary",
            | UnadmittedFormer::Run => {
                "a recorded run or a ride at the pure kernel boundary, moved by the recorded-run consumer"
            },
            | UnadmittedFormer::HigherFlow => "a flow at a universe above level zero",
            | UnadmittedFormer::Memory => "a memory form at the pure kernel boundary",
            | UnadmittedFormer::Stage => "a recursion's stage outside the judgement that minted it",
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
            OccurrenceSite::Parameter(position) => {
                write!(f, "parameter {}", usize::from(position))
            },
            OccurrenceSite::Field { tag, field } => write!(
                f,
                "field {} of constructor {}",
                usize::from(field),
                usize::from(tag)
            ),
        }
    }
}

/// Where a value a structural recursion wanted below its stage stood, as
/// prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Stood(pub Standing);

impl fmt::Display for Stood
{
    /// Writes why the value is not below the stage.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes that nothing places the value below the parameter for
    ///   a value at no stage, and that its stage is not below the one wanted
    ///   otherwise.
    /// - provides: the reason a stage refusal names.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no written text or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value at no stage and one at a stage title distinct
    ///   reasons.
    /// - witness: `locus::tests::recursion_titles_name_their_site_and_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            Standing::Top => {
                "nothing places it below that parameter, neither as a field of it nor beside one"
            },
            Standing::Staged(_) => "it stands at a stage not below the one wanted",
        })
    }
}

/// Source-location boundaries and semantic formatter payloads.
#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::string::String;

    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CoreNode;
    use gandr_core_checker::ExpectedShape;
    use gandr_core_checker::Mismatch;
    use gandr_core_checker::TermNode;
    use gandr_core_checker::TypeNode;
    use gandr_core_checker::UnadmittedFormer;
    use gandr_core_checker::session::Capture;
    use gandr_core_checker::session::Endpoint;
    use gandr_core_checker::session::ForkSide;
    use gandr_core_checker::session::LinearityDefect;
    use gandr_core_checker::session::ProtocolDefect;
    use gandr_core_term::CoreArena;
    use gandr_core_term::session::ActionKind;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::FieldPosition;
    use gandr_kernel_term::OccurrenceSite;
    use gandr_kernel_term::ParameterPosition;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageDepth;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Standing;
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
        let root = StageId::from(0_usize);
        let below = Stage::Below {
            anchor: root,
            depth: StageDepth::ONE,
        };
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
            CheckRefusal::StageNotBelow {
                at: unit,
                found: Standing::Top,
                bound: below,
            },
            CheckRefusal::StageNotBelow {
                at: unit,
                found: Standing::Staged(Stage::At(root)),
                bound: below,
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

    #[test]
    fn session_refusals_point_at_the_fork_and_name_the_action()
    {
        let spans: [ByteSpan; 3_usize] = core::array::from_fn(|index| {
            ByteSpan::new(
                ByteOffset::from(index * 10_usize),
                ByteOffset::from(index * 10_usize + 5_usize),
            )
            .expect("ordered fixture spans")
        });
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let [action, fork, arm] = [(); 3_usize].map(|()| arena.computation_return(unit));
        let state = arena.value_type_unit();
        let mut origins = OriginTable::new();
        for (index, computation) in [action, fork, arm].into_iter().enumerate() {
            origins.record_computation(
                computation,
                Origin::new(NodeIndex::from(index), spans[index]),
            );
        }
        let declaration = ByteSpan::new(ByteOffset::from(90_usize), ByteOffset::from(99_usize))
            .expect("the declaration is distinct from every node");
        let endpoint = Endpoint {
            fork,
            side: ForkSide::Parent,
        };
        let mismatch = |expected, observed| CheckRefusal::SessionMismatch {
            at: action,
            endpoint,
            state,
            defect: ProtocolDefect::Action { expected, observed },
        };
        let sending = mismatch(ActionKind::Send, ActionKind::Close);
        let found = Annotations::refusal(Refusal::Checking(sending), declaration, &origins);
        assert_eq!(
            found.primary,
            Maybe::Present(Annotation {
                span: spans[0_usize],
                label: Label::Culprit(Culprit::of(Refusal::Checking(sending))),
            }),
            "the action is the culprit"
        );
        assert_eq!(
            found.context,
            [
                Maybe::Present(Annotation {
                    span: spans[1_usize],
                    label: Label::Forked,
                }),
                Maybe::Absent(report_context::Absent::Unnamed),
            ],
            "the fork that opened the endpoint is named"
        );
        let disagreeing = CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(action)),
            defect: LinearityDefect::ArmsDisagree {
                endpoint,
                first: arm,
                other: action,
            },
        };
        assert_eq!(
            Annotations::refusal(Refusal::Checking(disagreeing), declaration, &origins).context,
            [
                Maybe::Present(Annotation {
                    span: spans[1_usize],
                    label: Label::Forked,
                }),
                Maybe::Present(Annotation {
                    span: spans[2_usize],
                    label: Label::FirstArm,
                }),
            ],
            "the fork and the arm the later one disagrees with"
        );
        let title = Checked(sending).to_string();
        assert!(
            matches!(
                (title.find("a send"), title.find("a close")),
                (Some(send), Some(close)) if send < close
            ),
            "the admitted action, then the attempted one: {title}"
        );
        assert_ne!(
            title,
            Checked(mismatch(ActionKind::Close, ActionKind::Send)).to_string(),
            "the two roles are not conflated"
        );
        let captors: BTreeSet<String> = [
            Capture::Thunk,
            Capture::Recursion,
            Capture::Branch,
            Capture::Stack,
            Capture::Continuation,
        ]
        .map(|by| {
            Checked(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(action)),
                defect: LinearityDefect::Captured { endpoint, by },
            })
            .to_string()
        })
        .into();
        assert_eq!(captors.len(), 5_usize, "each captor is named apart");
    }
}
