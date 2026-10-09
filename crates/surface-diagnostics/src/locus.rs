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

use core::fmt;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::CoreNode;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Mismatch;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::UnadmittedFormer;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Surviving;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::report::Class;
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
    /// The report's class: the primary locus of a refusal or of a
    /// declaration unsettled with no refusal produced.
    Class(Class),
    /// The obligations a declaration leaves unsettled: the primary locus of a
    /// goal and of a declaration unsettled by its obligations.
    Surviving(Surviving),
    /// The first occurrence a duplicate repeats.
    First,
    /// The type a mismatched term was checked against.
    Expected,
    /// The type a mismatched term synthesised.
    Synthesised,
    /// The type a rule met where it required a former of another shape.
    Met(ExpectedShape),
}

impl fmt::Display for Label
{
    /// Writes the label's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Class(class) => fmt::Display::fmt(&class, f),
            | Self::Surviving(surviving) => write!(f, "surviving obligations: {surviving}"),
            | Self::First => f.write_str("first written here"),
            | Self::Expected => f.write_str("the type it is checked against"),
            | Self::Synthesised => f.write_str("the type it synthesises"),
            | Self::Met(wanted) => write!(f, "the type met, where {} is required", Shape(wanted)),
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

    /// The loci of a lowering refusal of class `class`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the primary locus is the span the lowering rejected, labelled
    ///   with `class`, and is absent for the two refusals about the run rather
    ///   than a position; a duplicate signature, definition or attribute marks
    ///   its first occurrence as context.
    /// - provides: the loci of a lowering refusal, whether it refused a
    ///   declaration or the source as a whole.
    /// - fails: never.
    /// - panics: none.
    pub fn lowering(
        refusal: LoweringRefusal<'_>,
        class: Class,
    ) -> Self
    {
        let primary = match refusal.span() {
            | Maybe::Present(span) => Maybe::Present(Annotation {
                span,
                label: Label::Class(class),
            }),
            | Maybe::Absent(_) => Maybe::Absent(report_span::Absent::Run),
        };
        let first = match refusal {
            | LoweringRefusal::DuplicateSignature { first, .. }
            | LoweringRefusal::DuplicateDefinition { first, .. }
            | LoweringRefusal::DuplicateImportAlias { first, .. }
            | LoweringRefusal::DuplicateAttribute { first, .. } => Maybe::Present(Annotation {
                span: first,
                label: Label::First,
            }),
            | LoweringRefusal::UnresolvedName { .. }
            | LoweringRefusal::UnresolvedTypeHead { .. }
            | LoweringRefusal::ShadowedBuiltin { .. }
            | LoweringRefusal::OutOfFragment { .. }
            | LoweringRefusal::MalformedLiteral { .. }
            | LoweringRefusal::MalformedForm { .. }
            | LoweringRefusal::UnknownAttribute { .. }
            | LoweringRefusal::MissingPayload { .. }
            | LoweringRefusal::NonValuePayload { .. }
            | LoweringRefusal::IllTypedPayload { .. }
            | LoweringRefusal::BudgetExceeded { .. }
            | LoweringRefusal::GrammarMismatch { .. }
            | LoweringRefusal::UnknownMold { .. } => Maybe::Absent(report_context::Absent::Unnamed),
        };
        Self {
            primary,
            context: [first, Maybe::Absent(report_context::Absent::Unnamed)],
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
    /// - provides: the primary locus labelled with the refusal's class, and its
    ///   context.
    /// - fails: never.
    /// - panics: none.
    pub fn refusal(
        refusal: Refusal<'_>,
        declaration: ByteSpan,
        origins: &OriginTable,
    ) -> Self
    {
        let class = Class::Refusal(refusal.classify());
        match refusal {
            | Refusal::Lowering(lowering) => Self::lowering(lowering, class),
            | Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { span, .. }) => {
                Self::at(span, Label::Class(class))
            },
            | Refusal::Checking(checking) => checked(checking, declaration, origins, class),
        }
    }
}

/// The loci of the checker refusal `refusal` of class `class`.
///
/// # Specification
/// trivial.
fn checked(
    refusal: CheckRefusal,
    declaration: ByteSpan,
    origins: &OriginTable,
    class: Class,
) -> Annotations
{
    let label = Label::Class(class);
    let (primary, context) = match refusal {
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
            form: CheckingForm::Thunk(at),
        }
        | CheckRefusal::UnknownConstant { at, .. }
        | CheckRefusal::UnboundIndex { at, .. }
        | CheckRefusal::Undecided { at } => (spanned(origins.value(at)), UNNAMED),
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Lambda(at) | CheckingForm::Return(at),
        } => (spanned(origins.computation(at)), UNNAMED),
        | CheckRefusal::OutOfFragment { at: core, .. }
        | CheckRefusal::DanglingNode { node: core } => (node(origins, core), UNNAMED),
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
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
                    | CheckingForm::Thunk(_) => "a thunk",
                    | CheckingForm::Lambda(_) => "a lambda",
                    | CheckingForm::Return(_) => "a return",
                    | CheckingForm::Hole(_) => "a hole",
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
        }
    }
}

/// The former a rule required, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Shape(ExpectedShape);

impl fmt::Display for Shape
{
    /// Writes the former with its notation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            | ExpectedShape::Thunk => "a thunk type `+U C`",
            | ExpectedShape::Returner => "a returner `-F A`",
            | ExpectedShape::Arrow => "an arrow `A → C`",
        })
    }
}

/// A former the judgement has no rule for, as prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Former(UnadmittedFormer);

impl fmt::Display for Former
{
    /// Writes the former's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            | UnadmittedFormer::Pair => "the pair value",
            | UnadmittedFormer::Injection => "a sum injection",
            | UnadmittedFormer::ValueLift => "an explicit universe lift of a value",
            | UnadmittedFormer::NumericLiteral => "a numeric literal",
            | UnadmittedFormer::Case => "a sum elimination",
            | UnadmittedFormer::NumericAtom => "the numeric base atom",
            | UnadmittedFormer::Product => "the product type",
            | UnadmittedFormer::Sum => "the sum type",
            | UnadmittedFormer::TypeLift => "a lift of a value type to a level not above its own",
            | UnadmittedFormer::Abstract => "a sealed abstract type",
            | UnadmittedFormer::SortParameter => "a universe over a sort parameter",
            | UnadmittedFormer::TopUniverse => "a universe at the greatest representable level",
        })
    }
}
