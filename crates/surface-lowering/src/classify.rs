//! The four-class failure classifier every refusal carries.
//!
//! # Whose fact a failure is, decided by its kind
//!
//! The four classes record whose fact a failure is: an absence the author has
//! not supplied yet, a feature gandr has not implemented, a form the author
//! wrote wrongly or the language's design refuses, or a fault of the
//! lowering's own. An unimplemented refusal carries the issue that tracks the
//! feature, which every face showing the refusal names.
//!
//! The classes are `gandr-core-term`'s, shared with every other producer of
//! refusals in the core pipeline; the classifier below is this crate's own.
//! It is an exhaustive, wildcard-free match over the variants that reads a
//! refusal's kind — its variant, and for a form out of the fragment the form,
//! the sort its position demanded and the boundary it crossed, for an
//! unstated model component the fault — and never a span or a name: two
//! refusals of one kind classify alike, and a refusal added without a class
//! does not compile.
//!
//! # A form out of the fragment names its issue by what it is
//!
//! A form the fragment reserves or does not admit names the issue tracking
//! that form, read off the form and the sort its position demands: an
//! instantiation is a recursive call's claim where a computation is read and a
//! partial supply where a value is. A form no issue of its own tracks yet names
//! the epic that files one once a source reaches it; the refusal still carries
//! the form, so the feature stays named. The universe of representable sorts
//! classifies a theory's sort member only, so read anywhere else it is
//! misplaced, malformed source. A form of the wrong sort where a declaration
//! is read is an expression at a module's root, which is a run target,
//! unimplemented, except the operator declaration, which names its own issue; a
//! form of the wrong sort anywhere else is misplaced and malformed source. An
//! action on a name that is no fork's end is delegation, and a family read at
//! an index is the indexed family, both unimplemented. Every other boundary —
//! an operand count, a type the source does not state, a descent that is not
//! uniform or names another function, `cong` at a constructor, an exit off
//! every path, a match whose arms continue its block, the empty list, a
//! protocol recursing before any action, a lent or ended name that is no linear
//! slot — is a boundary the language draws, and malformed source.
//!
//! A refusal's name in a fixture's `refuses` expectation is keyed by the same
//! reading, [`FragmentFeature`]: the form, with the sort where the sort decides
//! the issue; the run target; or the boundary, without the operand count an
//! arity offers. One name then covers one feature, and the witness checks that
//! every form, sort and boundary one feature names classifies alike.
//! **Choice.** The name carries the key as a qualifier on the one refusal,
//! `OutOfFragment.projection_expression`; the alternative, a refusal variant
//! per feature, multiplied the vocabulary for a distinction the qualifier
//! already makes.
//!
//! # A description member names its issue by its fault
//!
//! A member of a `data`, `codata` or `theory` block that the description route
//! or its cell layer does not read is refused at its own span by the fault that
//! stops it, not as one form of the declaration: an operation's circuit body, a
//! rule between rules, the reserved `<->`, a law nesting an operation, and a
//! circuit rule with two redexes are five features, each naming its issue. A
//! rule from no operation, a copied variable, a variable worn at both
//! polarities or a wiring with no boundary is the author's mistake, malformed
//! source. **Choice.** The refusal keeps the fault the route and the cell gate
//! already distinguish; the alternative, one unadmitted declaration form for
//! all of them, named one issue for several features and classed the author's
//! mistakes as unbuilt.
//!
//! # The absence class has no inhabitant here, and that is the point
//!
//! Nothing this crate refuses is an absence. The obligation ledger is fed by
//! declaration *shape* — a signature no definition completes — and never by a
//! classified failure, so a lowering failure cannot be spelled as an
//! obligation. The class exists so the vocabulary is complete and so a later
//! absence has somewhere to land; its emptiness today is the statement itself.
//!
//! # A repaired form is the author's, a foreign tree is the caller's
//!
//! A form the parser had to repair, or one holding two operands where its rule
//! takes one, was written wrongly by the author, so it classifies as malformed
//! source alongside every other author mistake. A tree molded under another
//! grammar, or carrying a mold the grammar does not hold, says nothing about
//! the source: the caller handed the lowering a tree and a grammar that do not
//! belong together, which is a fault of the run, never of the text.

use anodized::spec;
pub use gandr_core_term::FailureClass;
pub use gandr_core_term::TrackingIssue;

use crate::description::MemberFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::model::ModelFault;

impl LoweringRefusal<'_>
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the refusal's kind — the variant,
    ///   a form out of the fragment's form, sort and boundary, an unstated
    ///   component's or an undescribed member's fault — and never of a span or
    ///   a name. A form reserved or unadmitted, but for the universe of
    ///   representable sorts out of its sort member, an indexed reading, an
    ///   action on no endpoint, a form of the wrong sort where a declaration is
    ///   read, a graded bridge, an unread ascription, an implicit telescope out
    ///   of shape, a model component that relates a many-out operation's
    ///   results, states a circuit rule or binds a variable, and a member the
    ///   description route or its cell layer has not built a reading for are
    ///   unimplemented, each naming its issue; the exhausted allowance, the
    ///   grammar mismatch, the unknown mold, an undecided coincidence check, an
    ///   unminted declaration and a circuit redex off its own boundary are
    ///   engine faults; every other refusal is malformed source.
    /// - provides: the fact a report groups by, and the issue every face of an
    ///   unimplemented refusal names.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned class table; the census's forms out of
    ///   the fragment are pinned to their issues, and two refusals of one kind
    ///   at different positions and names are asserted to classify alike.
    /// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
    /// - witness: `classify::tests::a_form_out_of_the_fragment_names_the_issue_tracking_it`
    /// - witness: `classify::tests::the_classification_ignores_position_and_name`
    /// - witness: `classify::tests::the_absence_class_has_no_inhabitant`
    #[spec(
        ensures: |ret| match *self {
            | Self::OutOfFragment {
                boundary: FragmentBoundary::Reserved | FragmentBoundary::Unadmitted,
                form,
                ..
            } if form == FormName::REPRESENTABLE_UNIVERSE_TYPE => {
                matches!(ret, FailureClass::MalformedSource)
            },
            | Self::OutOfFragment {
                boundary: FragmentBoundary::Reserved
                    | FragmentBoundary::Unadmitted
                    | FragmentBoundary::Indexed
                    | FragmentBoundary::Endpoint,
                ..
            }
            | Self::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                sort: FragmentSort::Declaration,
                ..
            }
            | Self::UnstatedComponent {
                fault: ModelFault::ManyOut
                    | ModelFault::Circuit
                    | ModelFault::Binding
                    | ModelFault::Abstraction,
                ..
            }
            | Self::UndescribedMember {
                fault: MemberFault::HigherOrderField
                    | MemberFault::DependentField
                    | MemberFault::TypeShape
                    | MemberFault::NativeDecode
                    | MemberFault::OperationFiller
                    | MemberFault::HigherCell
                    | MemberFault::Reversible
                    | MemberFault::AggregatedOutput
                    | MemberFault::NestedOperation
                    | MemberFault::UnrepresentableOperation
                    | MemberFault::ParallelRedexes,
                ..
            }
            | Self::GradedBridge { .. }
            | Self::UnreadAscription { .. }
            | Self::ImplicitTelescope { .. } => matches!(ret, FailureClass::Unimplemented(_)),
            | Self::UndescribedMember {
                fault: MemberFault::OffBoundary,
                ..
            }
            | Self::BudgetExceeded { .. }
            | Self::GrammarMismatch { .. }
            | Self::RulesUndecided { .. }
            | Self::UnknownMold { .. }
            | Self::Unminted { .. } => matches!(ret, FailureClass::EngineFault),
            | Self::OutOfFragment { .. }
            | Self::UnstatedComponent { .. }
            | Self::UndescribedMember { .. }
            | Self::WithoutK { .. }
            | Self::DirectedCell { .. }
            | Self::CellNotALoop { .. }
            | Self::DescentOnSeveralParameters { .. }
            | Self::UnguardedCorecursion { .. }
            | Self::BareFeedback { .. }
            | Self::IllFormedDescription { .. }
            | Self::UnresolvedName { .. }
            | Self::UnresolvedDocLink { .. }
            | Self::UnresolvedTypeHead { .. }
            | Self::DuplicateSignature { .. }
            | Self::DuplicateDefinition { .. }
            | Self::DuplicateImportAlias { .. }
            | Self::ImportUnresolved { .. }
            | Self::ImportCycle { .. }
            | Self::ImportShadows { .. }
            | Self::UnexportedName { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::PhaseDependence { .. }
            | Self::UnknownMember { .. }
            | Self::NotAFunctor { .. }
            | Self::ProjectionFromApplication { .. }
            | Self::FamilyTelescope { .. }
            | Self::LowercaseModuleName { .. }
            | Self::TelescopeCycle { .. }
            | Self::ImplicitUnsupplied { .. }
            | Self::ImplicitInParentheses { .. }
            | Self::RegionAsValue { .. }
            | Self::StrayReceiverMode { .. }
            | Self::AmbiguousMethod { .. }
            | Self::ViewNotPlace { .. }
            | Self::ViewOfNoPlace { .. }
            | Self::NonExhaustiveMatch { .. }
            | Self::UnmarkedSelfReference { .. }
            | Self::Unreachable { .. }
            | Self::OutsideLoop { .. }
            | Self::RulesUnoriented { .. }
            | Self::RulesNonLinear { .. }
            | Self::RulesDiverge { .. }
            | Self::RulesOverlapSecondOrder { .. }
            | Self::RulesUncompleted { .. }
            | Self::RulesNeverComplete { .. }
            | Self::AcrossHandler { .. } => {
                matches!(ret, FailureClass::MalformedSource)
            },
        },
    )]
    #[inline]
    #[must_use]
    pub fn classify(&self) -> FailureClass
    {
        match *self {
            Self::UnresolvedName { .. }
            | Self::UnresolvedDocLink { .. }
            | Self::UnresolvedTypeHead { .. }
            | Self::DuplicateSignature { .. }
            | Self::DuplicateDefinition { .. }
            | Self::DuplicateImportAlias { .. }
            | Self::ImportUnresolved { .. }
            | Self::ImportCycle { .. }
            | Self::ImportShadows { .. }
            | Self::UnexportedName { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::PhaseDependence { .. }
            | Self::UnknownMember { .. }
            | Self::NotAFunctor { .. }
            | Self::ProjectionFromApplication { .. }
            | Self::FamilyTelescope { .. }
            | Self::LowercaseModuleName { .. }
            | Self::TelescopeCycle { .. }
            | Self::ImplicitUnsupplied { .. }
            | Self::ImplicitInParentheses { .. }
            | Self::RegionAsValue { .. }
            | Self::StrayReceiverMode { .. }
            | Self::AmbiguousMethod { .. }
            | Self::ViewNotPlace { .. }
            | Self::ViewOfNoPlace { .. }
            | Self::NonExhaustiveMatch { .. }
            | Self::UnmarkedSelfReference { .. }
            | Self::Unreachable { .. }
            | Self::OutsideLoop { .. }
            | Self::RulesUnoriented { .. }
            | Self::RulesNonLinear { .. }
            | Self::RulesDiverge { .. }
            | Self::RulesOverlapSecondOrder { .. }
            | Self::RulesUncompleted { .. }
            | Self::RulesNeverComplete { .. }
            | Self::AcrossHandler { .. }
            | Self::WithoutK { .. }
            | Self::DirectedCell { .. }
            | Self::CellNotALoop { .. }
            | Self::DescentOnSeveralParameters { .. }
            | Self::UnguardedCorecursion { .. }
            | Self::BareFeedback { .. }
            | Self::IllFormedDescription { .. } => FailureClass::MalformedSource,
            Self::OutOfFragment {
                form,
                sort,
                boundary,
                ..
            } => out_of_fragment(form, sort, boundary),
            Self::UnstatedComponent { fault, .. } => unstated(fault),
            Self::UndescribedMember { fault, .. } => undescribed(fault),
            Self::GradedBridge { .. } => FailureClass::Unimplemented(TrackingIssue::THUNK_GRADE),
            Self::UnreadAscription { .. } => FailureClass::Unimplemented(TrackingIssue::ASCRIPTION),
            Self::ImplicitTelescope { .. } => FailureClass::Unimplemented(TrackingIssue::UNFILED),
            Self::BudgetExceeded { .. }
            | Self::GrammarMismatch { .. }
            | Self::RulesUndecided { .. }
            | Self::UnknownMold { .. }
            | Self::Unminted { .. } => FailureClass::EngineFault,
        }
    }
}

/// The class of a form out of the fragment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a reserved or unadmitted form names the issue [`tracked_form`]
///   answers, but the universe of representable sorts, which classifies a
///   theory's sort member only and is misplaced anywhere the lowering reads it,
///   is malformed source; a form of the wrong sort where a declaration is read
///   names the operator declaration's issue for an operator declaration and the
///   run target's for every other; an indexed reading names the indexed
///   family's, an action on no endpoint delegation's; every other boundary is
///   malformed source.
/// - provides: the lowering classifier's arm for `OutOfFragment`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each boundary and the declaration sort's two cases are
///   pinned by a census row.
/// - witness: `classify::tests::a_form_out_of_the_fragment_names_the_issue_tracking_it`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::Unimplemented(_))
        == ((matches!(boundary, FragmentBoundary::Reserved | FragmentBoundary::Unadmitted)
            && form != FormName::REPRESENTABLE_UNIVERSE_TYPE)
            || matches!(boundary, FragmentBoundary::Indexed | FragmentBoundary::Endpoint)
            || (boundary == FragmentBoundary::WrongSort && sort == FragmentSort::Declaration))
        && matches!(ret, FailureClass::Unimplemented(_) | FailureClass::MalformedSource),
)]
#[must_use]
fn out_of_fragment(
    form: FormName,
    sort: FragmentSort,
    boundary: FragmentBoundary,
) -> FailureClass
{
    match boundary {
        FragmentBoundary::Reserved | FragmentBoundary::Unadmitted
            if form == FormName::REPRESENTABLE_UNIVERSE_TYPE =>
        {
            FailureClass::MalformedSource
        },
        FragmentBoundary::Reserved | FragmentBoundary::Unadmitted => {
            FailureClass::Unimplemented(tracked_form(form, sort))
        },
        FragmentBoundary::WrongSort => match sort {
            FragmentSort::Declaration if form == FormName::OPERATOR_DECLARATION => {
                FailureClass::Unimplemented(TrackingIssue::OPERATOR_DECLARATION)
            },
            FragmentSort::Declaration => FailureClass::Unimplemented(TrackingIssue::RUN_TARGET),
            FragmentSort::Module
            | FragmentSort::ValueType
            | FragmentSort::CompType
            | FragmentSort::Value
            | FragmentSort::Computation
            | FragmentSort::Pattern
            | FragmentSort::Continuation => FailureClass::MalformedSource,
        },
        FragmentBoundary::Indexed => FailureClass::Unimplemented(TrackingIssue::INDEXED),
        FragmentBoundary::Endpoint => FailureClass::Unimplemented(TrackingIssue::DELEGATION),
        FragmentBoundary::Arity(_)
        | FragmentBoundary::Unannotated
        | FragmentBoundary::NonUniform
        | FragmentBoundary::ForeignClaim
        | FragmentBoundary::NotAFunction
        | FragmentBoundary::NotInTail
        | FragmentBoundary::JoinsBlock
        | FragmentBoundary::EmptyList
        | FragmentBoundary::NonContractive
        | FragmentBoundary::Held
        | FragmentBoundary::View => FailureClass::MalformedSource,
    }
}

/// The one feature a form out of the fragment refuses: the key its name in a
/// fixture's `refuses` expectation carries, so no name covers two features.
///
/// # Specification
/// - requires: built by [`FragmentFeature::of`].
/// - ensures: two refusals [`FragmentFeature::of`] gives one feature classify
///   alike.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`FragmentFeature::of`] carries the predicate, and the witness checks the
///   ensures clause over every form, sort and boundary.
///
/// # Adequacy
/// - hypothesis: L2 — every form the lowering spells, at every sort and
///   boundary, against every other of its feature: a feature covering two
///   classes or two issues is found.
/// - witness: `classify::tests::one_feature_names_one_class`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentFeature
{
    /// A form named by itself: one the fragment reserves or does not admit
    /// and that one issue tracks at every sort, and the operator declaration
    /// wherever it stands.
    Form(FormName),
    /// A form the fragment reserves or does not admit and whose issue the
    /// sort its position demands decides: an instantiation, a grade.
    FormAt(FormName, FragmentSort),
    /// A form of the wrong sort where a declaration is read: an expression
    /// at a module's root, a run target.
    RunTarget,
    /// A form crossing any other boundary, named by the boundary alone: the
    /// operand count an arity offers is no part of the feature.
    Crossed(FragmentBoundary),
}

impl FragmentFeature
{
    /// The feature a form out of the fragment refuses, read off the form,
    /// the sort its position demands and the boundary it crossed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a reserved or unadmitted form is its form, with the sort
    ///   where the sort decides its issue; an operator declaration of the wrong
    ///   sort where a declaration is read is its form, and any other form so is
    ///   the run target; every other crossing is its boundary.
    /// - provides: the qualifier a refusal name of `OutOfFragment` carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`FragmentFeature`].
    /// - witness: `classify::tests::one_feature_names_one_class`
    #[spec(ensures: |ret| match boundary {
        | FragmentBoundary::Reserved | FragmentBoundary::Unadmitted => matches!(ret,
            Self::Form(named) | Self::FormAt(named, _) if named == form),
        | FragmentBoundary::WrongSort if sort == FragmentSort::Declaration => matches!(ret,
            Self::RunTarget) || matches!(ret, Self::Form(named) if named == form),
        | _ => ret == Self::Crossed(boundary),
    })]
    #[inline]
    #[must_use]
    pub fn of(
        form: FormName,
        sort: FragmentSort,
        boundary: FragmentBoundary,
    ) -> Self
    {
        match boundary {
            FragmentBoundary::Reserved | FragmentBoundary::Unadmitted
                if form == FormName::INSTANTIATION || form == FormName::GRADE =>
            {
                Self::FormAt(form, sort)
            },
            FragmentBoundary::Reserved | FragmentBoundary::Unadmitted => Self::Form(form),
            FragmentBoundary::WrongSort if sort == FragmentSort::Declaration => {
                if form == FormName::OPERATOR_DECLARATION {
                    Self::Form(form)
                }
                else {
                    Self::RunTarget
                }
            },
            FragmentBoundary::WrongSort
            | FragmentBoundary::Arity(_)
            | FragmentBoundary::Indexed
            | FragmentBoundary::Unannotated
            | FragmentBoundary::NonUniform
            | FragmentBoundary::ForeignClaim
            | FragmentBoundary::NotAFunction
            | FragmentBoundary::NotInTail
            | FragmentBoundary::JoinsBlock
            | FragmentBoundary::EmptyList
            | FragmentBoundary::Endpoint
            | FragmentBoundary::NonContractive
            | FragmentBoundary::Held
            | FragmentBoundary::View => Self::Crossed(boundary),
        }
    }
}

/// The issue tracking a form the fragment reserves or does not admit.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a form an open issue tracks names that issue — a grade where a
///   declaration is read, the field grade's, and an instantiation, a recursive
///   call's claim where a computation is read and a partial supply where a
///   value is; every other form names [`TrackingIssue::UNFILED`], the epic that
///   files an issue for a feature once a source reaches it.
/// - provides: the issue of a reserved or unadmitted form.
/// - fails: never.
/// - panics: none.
/// - executable: none — the table is the specification; a predicate would
///   restate it row by row.
///
/// # Adequacy
/// - hypothesis: L3 — the census's tracked forms and an untracked one are
///   pinned to their issues, the grade and the parameter at the sort that names
///   an issue and at one that does not.
/// - witness: `classify::tests::a_form_out_of_the_fragment_names_the_issue_tracking_it`
#[must_use]
fn tracked_form(
    form: FormName,
    sort: FragmentSort,
) -> TrackingIssue
{
    match form {
        FormName::PROJECTION => TrackingIssue::PROJECTION,
        FormName::INDEX => TrackingIssue::INDEX,
        FormName::PACK
        | FormName::PACK_MODEL
        | FormName::PACKAGE_TYPE
        | FormName::UNPACK_STATEMENT => TrackingIssue::PACKAGES,
        FormName::ANNOTATION => TrackingIssue::ANNOTATION_VALUE,
        FormName::RECORD_UPDATE => TrackingIssue::RECORD_UPDATE,
        FormName::TYPED_NUMBER => TrackingIssue::TYPED_NUMBER,
        FormName::SHELL_BLOCK => TrackingIssue::SHELL_BLOCK,
        FormName::GRADE if matches!(sort, FragmentSort::Declaration) => TrackingIssue::FIELD_GRADE,
        FormName::AS_PATTERN | FormName::LIST_PATTERN | FormName::REST_PATTERN => {
            TrackingIssue::PATTERNS
        },
        FormName::CHARACTER => TrackingIssue::CHARACTER,
        FormName::CO_BUNDLE => TrackingIssue::CO_BUNDLE,
        FormName::DROP => TrackingIssue::DROP,
        FormName::FORALL_TYPE => TrackingIssue::FORALL,
        FormName::UNION_TYPE | FormName::INTERSECTION_TYPE => TrackingIssue::UNION_INTERSECTION,
        FormName::OPERATOR_DECLARATION => TrackingIssue::OPERATOR_DECLARATION,
        FormName::INSTANTIATION if matches!(sort, FragmentSort::Computation) => {
            TrackingIssue::RECURSIVE_CLAIM
        },
        FormName::INSTANTIATION if matches!(sort, FragmentSort::Value) => {
            TrackingIssue::PARTIAL_SUPPLY
        },
        FormName::FORK_STATEMENT | FormName::HOLD_STATEMENT => TrackingIssue::JOINED_SCOPE,
        FormName::FORK_SHARED_STATEMENT
        | FormName::DUP
        | FormName::ACQUIRE_STATEMENT
        | FormName::RELEASE_STATEMENT => TrackingIssue::SHARED_SESSIONS,
        FormName::STAGED_TYPE => TrackingIssue::PLACED_STAGE,
        FormName::UNKNOWN_TYPE => TrackingIssue::UNKNOWN_TYPE,
        FormName::INTERPOLATION => TrackingIssue::INTERPOLATION,
        FormName::CASE_WITH_VIEW => TrackingIssue::CASE_VIEW,
        _ => TrackingIssue::UNFILED,
    }
}

/// The class of a model component the derivation cannot state.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a component relating a many-out operation's results, a circuit
///   rule, a binding operation and an abstracting operation are unimplemented,
///   each naming its issue; an unknown head, a wrong arity, an ill-sorted term,
///   an unsorted variable, a constructor term and a component inheriting
///   another's failure are malformed source.
/// - provides: the lowering classifier's arm for `UnstatedComponent`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circuit fault is pinned in the class table.
/// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::Unimplemented(_))
        == matches!(fault, ModelFault::ManyOut | ModelFault::Circuit | ModelFault::Binding | ModelFault::Abstraction)
        && matches!(ret, FailureClass::Unimplemented(_) | FailureClass::MalformedSource),
)]
#[must_use]
fn unstated(fault: ModelFault) -> FailureClass
{
    match fault {
        ModelFault::ManyOut => FailureClass::Unimplemented(TrackingIssue::MODEL_MANY_OUT),
        ModelFault::Circuit => FailureClass::Unimplemented(TrackingIssue::MODEL_CIRCUIT),
        ModelFault::Binding => FailureClass::Unimplemented(TrackingIssue::MODEL_BINDING),
        ModelFault::Abstraction => FailureClass::Unimplemented(TrackingIssue::MODEL_ABSTRACTION),
        ModelFault::UnknownHead
        | ModelFault::Arity
        | ModelFault::IllSorted
        | ModelFault::Unsorted
        | ModelFault::Constructor
        | ModelFault::Inherited => FailureClass::MalformedSource,
    }
}

/// The class of a description member the route or its cell layer does not
/// read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an operation filler, a higher cell, the reversible glyph, a
///   nested operation and two redexes in one circuit rule are unimplemented,
///   each naming its issue; a field past the first-order code, an undecodable
///   description, an aggregated output and an operation the cell frame cannot
///   hold are unimplemented under the epic that files their issues; a circuit
///   redex off its own derived boundary is an engine fault; every other fault —
///   a rule from no operation, from an empty one, of the wrong result count,
///   copying a variable, wearing one name at both polarities, a wiring with no
///   boundary, an operation with no output — is malformed source.
/// - provides: the lowering classifier's arm for `UndescribedMember`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every fault is pinned to its class, each feature to its
///   own issue.
/// - witness: `classify::tests::a_member_the_description_does_not_read_names_its_issue_by_its_fault`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::EngineFault) == (fault == MemberFault::OffBoundary)
        && matches!(ret, FailureClass::Unimplemented(_) | FailureClass::MalformedSource | FailureClass::EngineFault),
)]
#[must_use]
fn undescribed(fault: MemberFault) -> FailureClass
{
    match fault {
        MemberFault::OperationFiller => {
            FailureClass::Unimplemented(TrackingIssue::OPERATION_FILLER)
        },
        MemberFault::HigherCell => FailureClass::Unimplemented(TrackingIssue::HIGHER_CELL),
        MemberFault::Reversible => FailureClass::Unimplemented(TrackingIssue::REVERSIBLE),
        MemberFault::NestedOperation => {
            FailureClass::Unimplemented(TrackingIssue::NESTED_OPERATION)
        },
        MemberFault::ParallelRedexes => {
            FailureClass::Unimplemented(TrackingIssue::PARALLEL_REDEXES)
        },
        MemberFault::HigherOrderField
        | MemberFault::DependentField
        | MemberFault::TypeShape
        | MemberFault::NativeDecode
        | MemberFault::AggregatedOutput
        | MemberFault::UnrepresentableOperation => {
            FailureClass::Unimplemented(TrackingIssue::UNFILED)
        },
        MemberFault::OffBoundary => FailureClass::EngineFault,
        MemberFault::NoOutput
        | MemberFault::LhsNotOperation
        | MemberFault::EmptyOperation
        | MemberFault::ResultArity
        | MemberFault::MixedPolarity
        | MemberFault::UnderivedWiring => FailureClass::MalformedSource,
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_core_term::TrackingIssue;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::FailureClass;
    use crate::attribute::AttributeSchema;
    use crate::attribute::PayloadForm;
    use crate::attribute::suggestion;
    use crate::error::AscriptionForm;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::lower::LoweringBudget;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;

    /// The whole refusal vocabulary, one inhabitant each, spans left empty.
    ///
    /// # Specification
    /// - requires: the built-in attribute registry contains `owes`.
    /// - ensures: the listed refusal variants have distinct representatives;
    ///   payloads are fixtures rather than evidence of a real lowering failure.
    /// - provides: the domain of the finite classification checks.
    /// - fails: never.
    /// - panics: if the named built-in attribute is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pairwise discriminants detect a repeated
    ///   representative that would hide another case behind the same expected
    ///   class. The class table observes every returned row; adding a variant
    ///   requires extending this finite fixture, not merely assuming that its
    ///   current size is exhaustive.
    /// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
    #[spec(
        ensures: |ret| {
            ret.iter().enumerate().all(|(position, refusal)| {
                ret.iter()
                    .skip(position.saturating_add(1_usize))
                    .all(|other| core::mem::discriminant(refusal) != core::mem::discriminant(other))
            })
        },
    )]
    fn vocabulary() -> [LoweringRefusal<'static>; 59_usize]
    {
        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        let owes = registered(SurfaceName::from("owes"));

        [
            LoweringRefusal::UnresolvedName {
                span: empty,
                name: SurfaceName::from("x"),
            },
            LoweringRefusal::UnresolvedTypeHead {
                span: empty,
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span: empty,
                name: SurfaceName::from("x"),
                first: empty,
            },
            LoweringRefusal::DuplicateDefinition {
                span: empty,
                name: SurfaceName::from("x"),
                first: empty,
            },
            LoweringRefusal::OutOfFragment {
                span: empty,
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved,
            },
            LoweringRefusal::MalformedLiteral {
                span: empty,
                form: FormName::from(NamedKind("number")),
            },
            LoweringRefusal::MalformedForm {
                span: empty,
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            LoweringRefusal::UnknownAttribute {
                span: empty,
                name: SurfaceName::from("check"),
                suggestion: Maybe::Absent(suggestion::Absent::BeyondBound),
            },
            LoweringRefusal::DuplicateAttribute {
                span: empty,
                name: SurfaceName::from("checks"),
                first: empty,
            },
            LoweringRefusal::MissingPayload {
                span: empty,
                name: owes,
                expected: AttributeSchema::Integer,
            },
            LoweringRefusal::NonValuePayload {
                span: empty,
                name: owes,
                form: FormName::from(NamedKind("pure_expression")),
            },
            LoweringRefusal::IllTypedPayload {
                span: empty,
                name: owes,
                expected: AttributeSchema::Integer,
                written: PayloadForm::Text,
            },
            LoweringRefusal::BudgetExceeded {
                budget: LoweringBudget::from(0_usize),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(0_u64),
                grammar: GrammarFingerprint::from(1_u64),
            },
            LoweringRefusal::UnknownMold {
                span: empty,
                mold: MoldId::from(0_u32),
            },
            LoweringRefusal::DuplicateImportAlias {
                span: empty,
                alias: SurfaceName::from("parse"),
                first: empty,
            },
            LoweringRefusal::ShadowedBuiltin {
                span: empty,
                name: SurfaceName::from("list"),
            },
            LoweringRefusal::GradedBridge {
                span: empty,
                grade: SurfaceName::from("1"),
            },
            LoweringRefusal::ForwardMemberReference {
                span: empty,
                name: SurfaceName::from("second"),
                declared: empty,
            },
            LoweringRefusal::PhaseDependence {
                span: empty,
                member: SurfaceName::from("Q"),
                reached: SurfaceName::from("n"),
            },
            LoweringRefusal::UnknownMember {
                span: empty,
                module: SurfaceName::from("Facts"),
                member: SurfaceName::from("hidden"),
            },
            LoweringRefusal::UnreadAscription {
                span: empty,
                name: SurfaceName::from("T"),
                form: AscriptionForm::Kinded,
            },
            LoweringRefusal::LowercaseModuleName {
                span: empty,
                name: SurfaceName::from("natAdd"),
            },
            LoweringRefusal::UnmarkedSelfReference {
                span: empty,
                name: SurfaceName::from("length"),
            },
            LoweringRefusal::UnresolvedDocLink {
                span: empty,
                name: SurfaceName::from("gone"),
            },
            LoweringRefusal::Unreachable { span: empty },
            LoweringRefusal::WithoutK { span: empty },
            LoweringRefusal::UnstatedComponent {
                span: empty,
                name: SurfaceName::from("assoc"),
                fault: crate::model::ModelFault::Circuit,
            },
            LoweringRefusal::FamilyTelescope {
                span: empty,
                name: SurfaceName::from("Hom"),
                fault: crate::error::TelescopeFault::Index(OperandCount::from(1_usize)),
            },
            LoweringRefusal::NotAFunctor {
                span: empty,
                name: SurfaceName::from("MkTally"),
            },
            LoweringRefusal::ProjectionFromApplication {
                span: empty,
                functor: SurfaceName::from("MkCounter"),
            },
            LoweringRefusal::OutsideLoop {
                span: empty,
                exit: crate::error::LoopExit::Break,
            },
            LoweringRefusal::AcrossHandler {
                span: empty,
                exit: crate::error::CrossedExit::Break,
            },
            LoweringRefusal::RulesUnoriented { span: empty },
            LoweringRefusal::RulesNonLinear {
                span: empty,
                copy: empty,
            },
            LoweringRefusal::RulesDiverge {
                span: empty,
                first: empty,
            },
            LoweringRefusal::RulesUndecided {
                span: empty,
                first: empty,
            },
            LoweringRefusal::DirectedCell { span: empty },
            LoweringRefusal::CellNotALoop { span: empty },
            LoweringRefusal::Unminted {
                span: empty,
                name: SurfaceName::from("windHom"),
            },
            LoweringRefusal::ImportUnresolved {
                span: empty,
                refused: empty,
            },
            LoweringRefusal::ImportCycle {
                span: empty,
                refused: empty,
            },
            LoweringRefusal::ImportShadows {
                span: empty,
                name: SurfaceName::from("Circle"),
                import: empty,
                other: empty,
            },
            LoweringRefusal::UnexportedName {
                span: empty,
                name: SurfaceName::from("pending"),
                declared: empty,
            },
            LoweringRefusal::DescentOnSeveralParameters {
                span: empty,
                staged: SurfaceName::from("m"),
                claimed: SurfaceName::from("n"),
            },
            LoweringRefusal::RulesUncompleted {
                span: empty,
                first: empty,
            },
            LoweringRefusal::RulesNeverComplete {
                span: empty,
                first: empty,
            },
            LoweringRefusal::BareFeedback {
                span: empty,
                rule: empty,
            },
            LoweringRefusal::ImplicitTelescope { span: empty },
            LoweringRefusal::TelescopeCycle {
                span: empty,
                first: SurfaceName::from("a"),
                second: SurfaceName::from("b"),
            },
            LoweringRefusal::ImplicitUnsupplied {
                span: empty,
                function: SurfaceName::from("same"),
                implicit: SurfaceName::from("a"),
            },
            LoweringRefusal::ImplicitInParentheses {
                span: empty,
                function: SurfaceName::from("same"),
                implicit: SurfaceName::from("a"),
            },
            LoweringRefusal::RegionAsValue {
                span: empty,
                name: SurfaceName::from("r"),
            },
            LoweringRefusal::StrayReceiverMode {
                span: empty,
                mode: SurfaceName::from("consumed"),
            },
            LoweringRefusal::AmbiguousMethod {
                span: empty,
                method: SurfaceName::from("len"),
                first: SurfaceName::from("Str"),
                second: SurfaceName::from("Bytes"),
                more: crate::CandidateCount::from(1_usize),
            },
            LoweringRefusal::UndescribedMember {
                span: empty,
                fault: crate::description::MemberFault::HigherCell,
            },
            LoweringRefusal::ViewNotPlace { span: empty },
            LoweringRefusal::ViewOfNoPlace { span: empty },
            LoweringRefusal::IllFormedDescription {
                span: empty,
                kind: crate::WfKind::DuplicateSortName,
                subjects: [
                    Maybe::Present(SurfaceName::from("Tm")),
                    Maybe::Absent(crate::description_subject::Absent::Unnamed),
                ],
            },
        ]
    }

    #[test]
    fn every_refusal_carries_its_pinned_class()
    {
        let expected = [
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::UNFILED),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
            FailureClass::EngineFault,
            FailureClass::EngineFault,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::THUNK_GRADE),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::ASCRIPTION),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::MODEL_CIRCUIT),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::UNFILED),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::HIGHER_CELL),
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
        ];

        for (refusal, class) in vocabulary().into_iter().zip(expected) {
            assert_eq!(
                refusal.classify(),
                class,
                "the class table is pinned row by row"
            );
        }
    }

    #[test]
    fn a_form_out_of_the_fragment_names_the_issue_tracking_it()
    {
        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        // One row per census reading: the form, the sort its position read,
        // the boundary, and the class with the issue it names.
        let rows = [
            (
                "projection_expression",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::PROJECTION),
            ),
            (
                "index_expression",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::INDEX),
            ),
            (
                "unpack_statement",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::PACKAGES),
            ),
            (
                "grade",
                FragmentSort::Declaration,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::FIELD_GRADE),
            ),
            (
                "def_value",
                FragmentSort::Declaration,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                "instantiation_expression",
                FragmentSort::Computation,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::RECURSIVE_CLAIM),
            ),
            (
                "instantiation_expression",
                FragmentSort::Value,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::PARTIAL_SUPPLY),
            ),
            (
                "fork_statement",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::JOINED_SCOPE),
            ),
            (
                "dup_expression",
                FragmentSort::Value,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::SHARED_SESSIONS),
            ),
            (
                "staged_type",
                FragmentSort::ValueType,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::PLACED_STAGE),
            ),
            (
                "unknown_type",
                FragmentSort::ValueType,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::UNKNOWN_TYPE),
            ),
            (
                "string_interpolation",
                FragmentSort::Value,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::INTERPOLATION),
            ),
            (
                "case_with_view",
                FragmentSort::Computation,
                FragmentBoundary::Reserved,
                FailureClass::Unimplemented(TrackingIssue::CASE_VIEW),
            ),
            (
                "representable_universe_type",
                FragmentSort::ValueType,
                FragmentBoundary::Unadmitted,
                FailureClass::MalformedSource,
            ),
            (
                "call_expression",
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort,
                FailureClass::Unimplemented(TrackingIssue::RUN_TARGET),
            ),
            (
                "operator_declaration",
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort,
                FailureClass::Unimplemented(TrackingIssue::OPERATOR_DECLARATION),
            ),
            (
                "lazy_product_type",
                FragmentSort::ValueType,
                FragmentBoundary::WrongSort,
                FailureClass::MalformedSource,
            ),
            (
                "identifier",
                FragmentSort::Value,
                FragmentBoundary::Endpoint,
                FailureClass::Unimplemented(TrackingIssue::DELEGATION),
            ),
            (
                "data_generator",
                FragmentSort::Declaration,
                FragmentBoundary::Indexed,
                FailureClass::Unimplemented(TrackingIssue::INDEXED),
            ),
            (
                "labelled_sum_pattern",
                FragmentSort::Computation,
                FragmentBoundary::Unannotated,
                FailureClass::MalformedSource,
            ),
            (
                "grade",
                FragmentSort::CompType,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                "parameter",
                FragmentSort::Declaration,
                FragmentBoundary::Unadmitted,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
        ];

        for (form, sort, boundary, class) in rows {
            let refusal = LoweringRefusal::OutOfFragment {
                span: empty,
                form: FormName::from(NamedKind(form)),
                sort,
                boundary,
            };
            assert_eq!(
                refusal.classify(),
                class,
                "`{form}` read as {sort} with the {boundary:?} boundary"
            );
        }
    }

    /// Every form the grammar names, at every sort and boundary: the forms
    /// one feature names classify alike, so a refusal name keyed by the
    /// feature covers one class and one issue (#1200).
    #[test]
    fn one_feature_names_one_class()
    {
        use alloc::collections::BTreeMap;

        use gandr_surface_grammar::PBG_ONLY_KINDS;
        use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;

        use super::FragmentFeature;

        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        let sorts = [
            FragmentSort::Module,
            FragmentSort::Declaration,
            FragmentSort::ValueType,
            FragmentSort::CompType,
            FragmentSort::Value,
            FragmentSort::Computation,
            FragmentSort::Pattern,
            FragmentSort::Continuation,
        ];
        let boundaries = [
            FragmentBoundary::Reserved,
            FragmentBoundary::Unadmitted,
            FragmentBoundary::WrongSort,
            FragmentBoundary::Arity(OperandCount::from(0_usize)),
            FragmentBoundary::Arity(OperandCount::from(2_usize)),
            FragmentBoundary::Indexed,
            FragmentBoundary::Unannotated,
            FragmentBoundary::NonUniform,
            FragmentBoundary::ForeignClaim,
            FragmentBoundary::NotAFunction,
            FragmentBoundary::NotInTail,
            FragmentBoundary::JoinsBlock,
            FragmentBoundary::EmptyList,
            FragmentBoundary::Endpoint,
            FragmentBoundary::NonContractive,
            FragmentBoundary::Held,
            FragmentBoundary::View,
        ];
        let mut classes: BTreeMap<FragmentFeature, FailureClass> = BTreeMap::new();
        for &kind in TREE_SITTER_NAMED_KINDS.iter().chain(PBG_ONLY_KINDS) {
            let form = FormName::from(NamedKind(kind));
            for sort in sorts {
                for boundary in boundaries {
                    let class = LoweringRefusal::OutOfFragment {
                        span: empty,
                        form,
                        sort,
                        boundary,
                    }
                    .classify();
                    let feature = FragmentFeature::of(form, sort, boundary);
                    let first = *classes.entry(feature).or_insert(class);
                    assert_eq!(
                        first, class,
                        "{feature:?} names `{kind}` read as {sort} with the {boundary:?} \
                         boundary, of another class than a form before it"
                    );
                }
            }
        }
    }

    #[test]
    fn a_member_the_description_does_not_read_names_its_issue_by_its_fault()
    {
        use crate::description::MemberFault;

        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        // One row per fault: a feature names its own issue or the epic, the
        // author's mistake is malformed, and a redex off its own boundary is
        // the engine's.
        let rows = [
            (
                MemberFault::OperationFiller,
                FailureClass::Unimplemented(TrackingIssue::OPERATION_FILLER),
            ),
            (
                MemberFault::HigherCell,
                FailureClass::Unimplemented(TrackingIssue::HIGHER_CELL),
            ),
            (
                MemberFault::Reversible,
                FailureClass::Unimplemented(TrackingIssue::REVERSIBLE),
            ),
            (
                MemberFault::NestedOperation,
                FailureClass::Unimplemented(TrackingIssue::NESTED_OPERATION),
            ),
            (
                MemberFault::ParallelRedexes,
                FailureClass::Unimplemented(TrackingIssue::PARALLEL_REDEXES),
            ),
            (
                MemberFault::HigherOrderField,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                MemberFault::DependentField,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                MemberFault::TypeShape,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                MemberFault::NativeDecode,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                MemberFault::AggregatedOutput,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (
                MemberFault::UnrepresentableOperation,
                FailureClass::Unimplemented(TrackingIssue::UNFILED),
            ),
            (MemberFault::NoOutput, FailureClass::MalformedSource),
            (MemberFault::LhsNotOperation, FailureClass::MalformedSource),
            (MemberFault::EmptyOperation, FailureClass::MalformedSource),
            (MemberFault::ResultArity, FailureClass::MalformedSource),
            (MemberFault::MixedPolarity, FailureClass::MalformedSource),
            (MemberFault::UnderivedWiring, FailureClass::MalformedSource),
            (MemberFault::OffBoundary, FailureClass::EngineFault),
        ];

        for (fault, class) in rows {
            assert_eq!(
                LoweringRefusal::UndescribedMember { span: empty, fault }.classify(),
                class,
                "a member refused for {fault} carries its pinned class"
            );
        }
    }

    #[test]
    fn the_classification_ignores_position_and_name()
    {
        // Two refusals of one kind, at different bytes and with different
        // names: a classifier reading either would separate them.
        let first = LoweringRefusal::UnstatedComponent {
            span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
            name: SurfaceName::from("assoc"),
            fault: crate::model::ModelFault::Binding,
        };
        let second = LoweringRefusal::UnstatedComponent {
            span: span(ByteOffset::from(40_usize), ByteOffset::from(90_usize)),
            name: SurfaceName::from("lambda"),
            fault: crate::model::ModelFault::Binding,
        };

        assert_eq!(
            first.classify(),
            second.classify(),
            "the class is a function of the kind alone"
        );
        assert_eq!(
            second.classify(),
            FailureClass::Unimplemented(TrackingIssue::MODEL_BINDING),
            "a binding operation names its issue"
        );
    }

    #[test]
    fn the_absence_class_has_no_inhabitant()
    {
        // The ledger is fed by declaration shape, never by a classified
        // failure, so nothing this crate refuses may classify as an absence.
        for refusal in vocabulary() {
            assert_ne!(
                refusal.classify(),
                FailureClass::UserAbsence,
                "no refusal of this crate may be read as an author absence"
            );
        }
    }
}
