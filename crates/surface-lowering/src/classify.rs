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
//! refusal's kind — its variant, and for a form out of the fragment the sort
//! its position demanded and the boundary it crossed, with the feature a
//! reserved or unadmitted form carries, for an unstated model component the
//! fault — and never a span or a name: two
//! refusals of one kind classify alike, and a refusal added without a class
//! does not compile.
//!
//! # A form out of the fragment names its issue by what it is
//!
//! A form the fragment reserves or does not admit names the issue tracking the
//! [`Unbuilt`] feature its refusing site names: an instantiation is a
//! recursive call's claim at one site and a partial supply at another. A
//! feature no issue of its own tracks yet names the epic that files one once a
//! source reaches it; the refusal still carries the feature, so it stays
//! named. The universe of representable sorts classifies a theory's sort
//! member only, so read anywhere else it is misplaced, malformed source. A
//! form of the wrong sort where a declaration is read is a stray, malformed
//! source, except the operator declaration and the extern block, which name
//! their own issues; an expression at a source's top level, where only
//! declarations stand, is malformed source too, as is a form of the wrong sort
//! anywhere else. An
//! action on a name that is no fork's end is delegation, and a family read at
//! an index is the indexed family, both unimplemented. Every other boundary —
//! an operand count, a type the source does not state, a descent that is not
//! uniform or names another function, `cong` at a constructor, an exit off
//! every path, a match whose arms continue its block, the empty list, a
//! protocol recursing before any action, a lent or ended name that is no linear
//! slot — is a boundary the language draws, and malformed source.
//!
//! A refusal's name in a fixture's `refuses` expectation is keyed by
//! [`FragmentFeature`]: the unbuilt feature; the stray; or the boundary,
//! without the operand count an arity offers. One name then covers one
//! feature, and the witness checks that every feature, sort and boundary one
//! name covers classifies alike.
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
use gandr_core_term::generic::Uncovered;

use crate::derive::DeriveFault;
use crate::description::MemberFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::model::ModelFault;
use crate::unbuilt::Unbuilt;

impl LoweringRefusal<'_>
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the refusal's kind — the variant,
    ///   a form out of the fragment's form, sort and boundary, an unstated
    ///   component's or an undescribed member's fault — and never of a span or
    ///   a name. A form reserved or unadmitted, an indexed reading, an action
    ///   on no endpoint, an operator declaration or an extern block where a
    ///   declaration is read, a graded bridge, an unread ascription, an
    ///   implicit telescope out of shape, a model component that relates a
    ///   many-out operation's results, states a circuit rule or binds a
    ///   variable, and a member the description route or its cell layer has not
    ///   built a reading for are unimplemented, each naming its issue; the
    ///   exhausted allowance, the grammar mismatch, the unknown mold, an
    ///   undecided coincidence check, an unminted declaration, a host table in
    ///   conflict and a circuit redex off its own boundary are engine faults;
    ///   every other refusal, a misplaced form and a stray root child among
    ///   them, is malformed source.
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
                boundary: FragmentBoundary::Reserved(feature) | FragmentBoundary::Unadmitted(feature),
                ..
            } => ret == FailureClass::Unimplemented(feature.tracking()),
            | Self::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                sort: FragmentSort::Declaration,
                form,
                ..
            } if form == FormName::OPERATOR_DECLARATION || form == FormName::EXTERN_BLOCK => {
                matches!(ret, FailureClass::Unimplemented(_))
            },
            | Self::OutOfFragment {
                boundary: FragmentBoundary::Indexed | FragmentBoundary::Endpoint,
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
            | Self::UnderivedRule {
                fault: DeriveFault::Indexed
                    | DeriveFault::Erased
                    | DeriveFault::Unstated(
                        ModelFault::ManyOut
                            | ModelFault::Circuit
                            | ModelFault::Binding
                            | ModelFault::Abstraction,
                    ),
                ..
            }
            | Self::IllFormedDescription {
                kind: crate::WfKind::UndecidedCondition,
                ..
            }
            | Self::GenericUncovered {
                fault: Uncovered::Applied(_)
                    | Uncovered::Nested(..)
                    | Uncovered::Cycle(..)
                    | Uncovered::Dependent(..)
                    | Uncovered::DependentCase(..)
                    | Uncovered::Inductive(..)
                    | Uncovered::Uncoded(..),
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
            | Self::UnderivedRule {
                fault: DeriveFault::Undecided,
                ..
            }
            | Self::UnknownMold { .. }
            | Self::HostConflict { .. }
            | Self::GenericUncovered {
                fault: Uncovered::BinderCeiling,
                ..
            }
            | Self::Unminted { .. } => matches!(ret, FailureClass::EngineFault),
            | Self::OutOfFragment { .. }
            | Self::UnstatedComponent { .. }
            | Self::UninterfacedMember { .. }
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
            | Self::UnlockedDependency { .. }
            | Self::ImportShadows { .. }
            | Self::UnexportedName { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::NoUniverseAbove { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::PhaseDependence { .. }
            | Self::InertRead { .. }
            | Self::UnknownMember { .. }
            | Self::UnprovenLaw { .. }
            | Self::PartialField { .. }
            | Self::NotAFunctor { .. }
            | Self::ProjectionFromApplication { .. }
            | Self::FamilyTelescope { .. }
            | Self::LowercaseModuleName { .. }
            | Self::TelescopeCycle { .. }
            | Self::ImplicitUnsupplied { .. }
            | Self::ImplicitInParentheses { .. }
            | Self::InstanceUnanswered { .. }
            | Self::InstanceAmbiguous { .. }
            | Self::ModelImplicitValue { .. }
            | Self::RegionAsValue { .. }
            | Self::EntryType { .. }
            | Self::StrayReceiverMode { .. }
            | Self::AmbiguousMethod { .. }
            | Self::ViewNotPlace { .. }
            | Self::ViewOfNoPlace { .. }
            | Self::NonExhaustiveMatch { .. }
            | Self::MismatchedPattern { .. }
            | Self::UnmarkedSelfReference { .. }
            | Self::Unreachable { .. }
            | Self::OutsideLoop { .. }
            | Self::RulesUnoriented { .. }
            | Self::RulesNonLinear { .. }
            | Self::RulesDiverge { .. }
            | Self::RulesOverlapSecondOrder { .. }
            | Self::RulesOverlapCondition { .. }
            | Self::RulesUncompleted { .. }
            | Self::RulesNeverComplete { .. }
            | Self::UnderivedRule { .. }
            | Self::AcrossHandler { .. }
            | Self::GenericMisplaced { .. }
            | Self::UnknownTactic { .. }
            | Self::GenericUncovered { .. } => {
                matches!(ret, FailureClass::MalformedSource)
            },
        },
    )]
    #[inline]
    #[must_use]
    pub fn classify(&self) -> FailureClass
    {
        match *self {
            Self::IllFormedDescription {
                kind: crate::WfKind::UndecidedCondition,
                ..
            } => FailureClass::Unimplemented(TrackingIssue::UNDECIDED_CONDITION),
            Self::UnresolvedName { .. }
            | Self::UnresolvedDocLink { .. }
            | Self::UnresolvedTypeHead { .. }
            | Self::DuplicateSignature { .. }
            | Self::DuplicateDefinition { .. }
            | Self::DuplicateImportAlias { .. }
            | Self::ImportUnresolved { .. }
            | Self::ImportCycle { .. }
            | Self::UnlockedDependency { .. }
            | Self::ImportShadows { .. }
            | Self::UnexportedName { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::NoUniverseAbove { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::PhaseDependence { .. }
            | Self::InertRead { .. }
            | Self::UnknownMember { .. }
            | Self::UnprovenLaw { .. }
            | Self::PartialField { .. }
            | Self::NotAFunctor { .. }
            | Self::ProjectionFromApplication { .. }
            | Self::FamilyTelescope { .. }
            | Self::UninterfacedMember { .. }
            | Self::LowercaseModuleName { .. }
            | Self::TelescopeCycle { .. }
            | Self::ImplicitUnsupplied { .. }
            | Self::ImplicitInParentheses { .. }
            | Self::InstanceUnanswered { .. }
            | Self::InstanceAmbiguous { .. }
            | Self::ModelImplicitValue { .. }
            | Self::RegionAsValue { .. }
            | Self::EntryType { .. }
            | Self::StrayReceiverMode { .. }
            | Self::AmbiguousMethod { .. }
            | Self::ViewNotPlace { .. }
            | Self::ViewOfNoPlace { .. }
            | Self::NonExhaustiveMatch { .. }
            | Self::MismatchedPattern { .. }
            | Self::UnmarkedSelfReference { .. }
            | Self::Unreachable { .. }
            | Self::OutsideLoop { .. }
            | Self::RulesUnoriented { .. }
            | Self::RulesNonLinear { .. }
            | Self::RulesDiverge { .. }
            | Self::RulesOverlapSecondOrder { .. }
            | Self::RulesOverlapCondition { .. }
            | Self::RulesUncompleted { .. }
            | Self::RulesNeverComplete { .. }
            | Self::AcrossHandler { .. }
            | Self::WithoutK { .. }
            | Self::DirectedCell { .. }
            | Self::CellNotALoop { .. }
            | Self::DescentOnSeveralParameters { .. }
            | Self::UnguardedCorecursion { .. }
            | Self::BareFeedback { .. }
            | Self::IllFormedDescription { .. }
            | Self::GenericMisplaced { .. }
            | Self::UnknownTactic { .. } => FailureClass::MalformedSource,
            Self::GenericUncovered { fault, .. } => uncovered(fault),
            Self::OutOfFragment {
                form,
                sort,
                boundary,
                ..
            } => out_of_fragment(form, sort, boundary),
            Self::UnstatedComponent { fault, .. } => unstated(fault),
            Self::UnderivedRule { fault, .. } => underived(fault),
            Self::UndescribedMember { fault, .. } => undescribed(fault),
            Self::GradedBridge { .. } => FailureClass::Unimplemented(TrackingIssue::THUNK_GRADE),
            Self::UnreadAscription { .. } => FailureClass::Unimplemented(TrackingIssue::ASCRIPTION),
            Self::ImplicitTelescope { .. } => {
                FailureClass::Unimplemented(TrackingIssue::IMPLICIT_TELESCOPE)
            },
            Self::BudgetExceeded { .. }
            | Self::GrammarMismatch { .. }
            | Self::RulesUndecided { .. }
            | Self::UnknownMold { .. }
            | Self::HostConflict { .. }
            | Self::Unminted { .. } => FailureClass::EngineFault,
        }
    }
}

/// The class of a form out of the fragment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a reserved or unadmitted form names the issue tracking the
///   feature it carries; a misplaced form is malformed source; a form of the
///   wrong sort where a declaration is read names the issue of the item it is
///   when it is an item the lowering does not reach, an operator declaration or
///   an extern block, and is malformed source for every other, a stray; an
///   indexed reading names the indexed family's, an action on no endpoint
///   delegation's; every other boundary is malformed source.
/// - provides: the lowering classifier's arm for `OutOfFragment`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each boundary and the declaration sort's three cases are
///   pinned by a census row.
/// - witness: `classify::tests::a_form_out_of_the_fragment_names_the_issue_tracking_it`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::Unimplemented(_))
        == (matches!(boundary, FragmentBoundary::Reserved(_) | FragmentBoundary::Unadmitted(_))
            || matches!(boundary, FragmentBoundary::Indexed | FragmentBoundary::Endpoint)
            || (boundary == FragmentBoundary::WrongSort
                && sort == FragmentSort::Declaration
                && (form == FormName::OPERATOR_DECLARATION || form == FormName::EXTERN_BLOCK)))
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
        FragmentBoundary::Reserved(feature) | FragmentBoundary::Unadmitted(feature) => {
            FailureClass::Unimplemented(feature.tracking())
        },
        FragmentBoundary::WrongSort => match FragmentFeature::of(form, sort, boundary) {
            FragmentFeature::Unbuilt(unbuilt) => FailureClass::Unimplemented(unbuilt.tracking()),
            FragmentFeature::Stray | FragmentFeature::Crossed(_) => FailureClass::MalformedSource,
        },
        FragmentBoundary::Indexed => FailureClass::Unimplemented(TrackingIssue::INDEXED),
        FragmentBoundary::Endpoint => {
            FailureClass::Unimplemented(TrackingIssue::ENDPOINT_PARAMETER)
        },
        FragmentBoundary::Misplaced
        | FragmentBoundary::NotAtResult
        | FragmentBoundary::Arity(_)
        | FragmentBoundary::Unannotated
        | FragmentBoundary::NonUniform
        | FragmentBoundary::ForeignClaim
        | FragmentBoundary::NotAFunction
        | FragmentBoundary::NotInTail
        | FragmentBoundary::JoinsBlock
        | FragmentBoundary::EmptyList
        | FragmentBoundary::NonContractive
        | FragmentBoundary::TopLevel
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
///   ensures clause over every feature, form, sort and boundary.
///
/// # Adequacy
/// - hypothesis: L2 — every feature, and every form the lowering spells, at
///   every sort and boundary, against every other of its key: a key covering
///   two classes or two issues is found.
/// - witness: `classify::tests::one_feature_names_one_class`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentFeature
{
    /// The feature a reserved or unadmitted form carries, and the operator
    /// declaration's and the extern block's wherever they stand.
    Unbuilt(Unbuilt),
    /// A form of the wrong sort where a declaration is read, other than an
    /// expression at the top level, which crosses a boundary of its own: a
    /// stray.
    Stray,
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
    /// - ensures: a reserved or unadmitted form is the feature it carries; an
    ///   operator declaration or an extern block of the wrong sort where a
    ///   declaration is read is its own feature, and any other form so is a
    ///   stray; every other crossing is its boundary.
    /// - provides: the qualifier a refusal name of `OutOfFragment` carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`FragmentFeature`].
    /// - witness: `classify::tests::one_feature_names_one_class`
    #[spec(ensures: |ret| match boundary {
        | FragmentBoundary::Reserved(feature) | FragmentBoundary::Unadmitted(feature) => {
            ret == Self::Unbuilt(feature)
        },
        | FragmentBoundary::WrongSort if sort == FragmentSort::Declaration => matches!(ret,
            Self::Stray | Self::Unbuilt(Unbuilt::OperatorDeclaration | Unbuilt::ExternBlock)),
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
            FragmentBoundary::Reserved(feature) | FragmentBoundary::Unadmitted(feature) => {
                Self::Unbuilt(feature)
            },
            FragmentBoundary::WrongSort if sort == FragmentSort::Declaration => {
                if form == FormName::OPERATOR_DECLARATION {
                    Self::Unbuilt(Unbuilt::OperatorDeclaration)
                }
                else if form == FormName::EXTERN_BLOCK {
                    Self::Unbuilt(Unbuilt::ExternBlock)
                }
                else {
                    Self::Stray
                }
            },
            FragmentBoundary::WrongSort
            | FragmentBoundary::Misplaced
            | FragmentBoundary::NotAtResult
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
            | FragmentBoundary::TopLevel
            | FragmentBoundary::Held
            | FragmentBoundary::View => Self::Crossed(boundary),
        }
    }
}

/// The class of a model component the derivation cannot state.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a component relating a many-out operation's results, a circuit
///   rule, a law at a binding port and an abstracting operation are
///   unimplemented, each naming its issue; an unknown head, a wrong arity, an
///   ill-sorted term, an unsorted variable, a constructor term, a component
///   inheriting another's failure and a stated law's unbound variable are
///   malformed source.
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
        | ModelFault::Inherited
        | ModelFault::Unbound => FailureClass::MalformedSource,
    }
}

/// The class of a statement its theory's completed rules do not prove.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a theory stating an indexed sort or a nested model, a peak
///   variable no term stands for and a component the derivation of models
///   classifies unimplemented are unimplemented; a side rewriting past the step
///   budget is an engine fault; two sides apart, a side stating no law and
///   rules that are no terminating, confluent system are malformed source, as a
///   component malformed in the theory is.
/// - provides: the lowering classifier's arm for `UnderivedRule`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the apart fault is pinned in the class table.
/// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::EngineFault) == matches!(fault, DeriveFault::Undecided),
)]
#[must_use]
fn underived(fault: DeriveFault) -> FailureClass
{
    match fault {
        DeriveFault::Indexed | DeriveFault::Erased => {
            FailureClass::Unimplemented(TrackingIssue::DERIVE_INDEXED)
        },
        DeriveFault::Unstated(component) => unstated(component),
        DeriveFault::Undecided => FailureClass::EngineFault,
        DeriveFault::Apart | DeriveFault::Incoherent | DeriveFault::Unsorted(_) => {
            FailureClass::MalformedSource
        },
    }
}

/// The class of a data type `Eq.generic` derives no equality for.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a declaration with parameters or indices, a recursive occurrence
///   under a product or a sum, a cycle through two declarations, a dependent
///   field and a law's induction are unimplemented under the generic equality's
///   issue, a field whose type the levitated code does not carry under the
///   code's type-shape issue, and a law's dependent case under the case
///   motive's; a binder count past the ceiling is an engine fault; a field with
///   no equality, a presented declaration and no declaration at all are
///   malformed source.
/// - provides: the lowering classifier's arm for `GenericUncovered`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every fault is pinned to its class.
/// - witness: `classify::tests::a_type_eq_generic_does_not_cover_names_its_class_by_its_fault_2302`
#[spec(
    ensures: |ret| matches!(ret, FailureClass::EngineFault) == matches!(fault, Uncovered::BinderCeiling),
)]
#[must_use]
fn uncovered(fault: Uncovered) -> FailureClass
{
    match fault {
        Uncovered::Applied(_)
        | Uncovered::Nested(..)
        | Uncovered::Cycle(..)
        | Uncovered::Dependent(..)
        | Uncovered::Inductive(..) => FailureClass::Unimplemented(TrackingIssue::GENERIC_EQUALITY),
        Uncovered::DependentCase(..) => FailureClass::Unimplemented(TrackingIssue::CASE_MOTIVE),
        Uncovered::Uncoded(..) => FailureClass::Unimplemented(TrackingIssue::TYPE_SHAPE),
        Uncovered::BinderCeiling => FailureClass::EngineFault,
        Uncovered::Unknown(_) | Uncovered::Presented(_) | Uncovered::Field(..) => {
            FailureClass::MalformedSource
        },
    }
}

/// The class of a description member the route or its cell layer does not
/// read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an operation filler, a higher cell, the reversible glyph, a
///   nested operation, two redexes in one circuit rule, a field past the
///   description code, an undecodable description, an aggregated output and an
///   operation the cell frame cannot hold are unimplemented, each naming its
///   issue; a circuit redex off its own derived boundary is an engine fault;
///   every other fault — a rule from no operation, from an empty one, of the
///   wrong result count, copying a variable, wearing one name at both
///   polarities, a wiring with no boundary, an operation with no output — is
///   malformed source.
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
        MemberFault::HigherOrderField => {
            FailureClass::Unimplemented(TrackingIssue::HIGHER_ORDER_FIELD)
        },
        MemberFault::DependentField => FailureClass::Unimplemented(TrackingIssue::DEPENDENT_FIELD),
        MemberFault::TypeShape => FailureClass::Unimplemented(TrackingIssue::TYPE_SHAPE),
        MemberFault::NativeDecode => FailureClass::Unimplemented(TrackingIssue::NATIVE_DECODE),
        MemberFault::AggregatedOutput | MemberFault::UnrepresentableOperation => {
            FailureClass::Unimplemented(TrackingIssue::OPERATION_SHAPE)
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
    use gandr_core_term::generic::Uncovered;
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
    use crate::error::Unexported;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::lower::LoweringBudget;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;
    use crate::unbuilt::Unbuilt;

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
    fn vocabulary() -> [LoweringRefusal<'static>; 76_usize]
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
                boundary: FragmentBoundary::Reserved(Unbuilt::Val),
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
            LoweringRefusal::InertRead {
                span: empty,
                member: SurfaceName::from("named"),
                reached: SurfaceName::from("name"),
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
            LoweringRefusal::UninterfacedMember {
                span: empty,
                name: SurfaceName::from("put"),
                fault: crate::model::InterfaceFault::Continuation,
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
                reason: Unexported::Undefined,
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
            LoweringRefusal::NonExhaustiveMatch { span: empty },
            LoweringRefusal::RulesOverlapSecondOrder {
                span: empty,
                first: empty,
            },
            LoweringRefusal::RulesOverlapCondition {
                span: empty,
                first: empty,
            },
            LoweringRefusal::UnguardedCorecursion {
                span: empty,
                name: SurfaceName::from("ones"),
            },
            LoweringRefusal::UnderivedRule {
                span: empty,
                rule: SurfaceName::from("comm"),
                theory: SurfaceName::from("Grp"),
                fault: crate::derive::DeriveFault::Apart,
            },
            LoweringRefusal::EntryType { span: empty },
            LoweringRefusal::MismatchedPattern {
                span: empty,
                first: empty,
            },
            LoweringRefusal::PartialField {
                span: empty,
                field: SurfaceName::from("start"),
                constructor: SurfaceName::from("Dot"),
            },
            LoweringRefusal::ModelImplicitValue {
                span: empty,
                implicit: SurfaceName::from("s"),
            },
            LoweringRefusal::GenericMisplaced { span: empty },
            LoweringRefusal::UnknownTactic { span: empty },
            LoweringRefusal::GenericUncovered {
                span: empty,
                data: SurfaceName::from("Box"),
                fault: Uncovered::Applied(gandr_kernel_term::ConstantIndex::from(0_usize)),
            },
            LoweringRefusal::NoUniverseAbove {
                span: empty,
                level: SurfaceName::from("18446744073709551615"),
            },
            LoweringRefusal::HostConflict { span: empty },
            LoweringRefusal::UnlockedDependency {
                span: empty,
                alias: SurfaceName::from("hello"),
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
            FailureClass::Unimplemented(TrackingIssue::VAL),
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
            FailureClass::Unimplemented(TrackingIssue::IMPLICIT_TELESCOPE),
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
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unimplemented(TrackingIssue::GENERIC_EQUALITY),
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
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
                FragmentBoundary::Unadmitted(Unbuilt::Projection),
                FailureClass::Unimplemented(TrackingIssue::PROJECTION),
            ),
            (
                "index_expression",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted(Unbuilt::Index),
                FailureClass::Unimplemented(TrackingIssue::UNHELD_INDEX),
            ),
            (
                "unpack_statement",
                FragmentSort::Computation,
                FragmentBoundary::Unadmitted(Unbuilt::Unpack),
                FailureClass::Unimplemented(TrackingIssue::PACKAGES),
            ),
            (
                "grade",
                FragmentSort::Declaration,
                FragmentBoundary::Unadmitted(Unbuilt::FieldGrade),
                FailureClass::Unimplemented(TrackingIssue::FIELD_GRADE),
            ),
            (
                "def_value",
                FragmentSort::Declaration,
                FragmentBoundary::Reserved(Unbuilt::Val),
                FailureClass::Unimplemented(TrackingIssue::VAL),
            ),
            (
                "instantiation_expression",
                FragmentSort::Computation,
                FragmentBoundary::Reserved(Unbuilt::RecursiveClaim),
                FailureClass::Unimplemented(TrackingIssue::RECURSIVE_CLAIM),
            ),
            (
                "dup_expression",
                FragmentSort::Value,
                FragmentBoundary::Reserved(Unbuilt::Dup),
                FailureClass::Unimplemented(TrackingIssue::SHARED_SESSIONS),
            ),
            (
                "staged_type",
                FragmentSort::ValueType,
                FragmentBoundary::Unadmitted(Unbuilt::StagedType),
                FailureClass::Unimplemented(TrackingIssue::PLACED_STAGE),
            ),
            (
                "unknown_type",
                FragmentSort::ValueType,
                FragmentBoundary::Reserved(Unbuilt::UnknownType),
                FailureClass::Unimplemented(TrackingIssue::UNKNOWN_TYPE),
            ),
            (
                "case_with_view",
                FragmentSort::Computation,
                FragmentBoundary::Reserved(Unbuilt::CaseView),
                FailureClass::Unimplemented(TrackingIssue::CASE_VIEW),
            ),
            (
                "representable_universe_type",
                FragmentSort::ValueType,
                FragmentBoundary::Misplaced,
                FailureClass::MalformedSource,
            ),
            (
                "call_expression",
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort,
                FailureClass::MalformedSource,
            ),
            (
                "operator_declaration",
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort,
                FailureClass::Unimplemented(TrackingIssue::OPERATOR_DECLARATION),
            ),
            (
                "extern_block",
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort,
                FailureClass::Unimplemented(TrackingIssue::EXTERN_BLOCK),
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
                FailureClass::Unimplemented(TrackingIssue::ENDPOINT_PARAMETER),
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
                FragmentBoundary::Unadmitted(Unbuilt::ThunkGrade),
                FailureClass::Unimplemented(TrackingIssue::THUNK_GRADE),
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
        let ill_formed = |kind| {
            LoweringRefusal::IllFormedDescription {
                span: empty,
                kind,
                subjects: [
                    Maybe::Present(SurfaceName::from("a")),
                    Maybe::Absent(crate::description_subject::Absent::Unnamed),
                ],
            }
            .classify()
        };
        assert_eq!(
            ill_formed(crate::WfKind::UndecidedCondition),
            FailureClass::Unimplemented(TrackingIssue::UNDECIDED_CONDITION),
            "a condition no rewriting step decides yet names the issue tracking it"
        );
        assert_eq!(
            ill_formed(crate::WfKind::Capture),
            FailureClass::MalformedSource,
            "a crossing left unstated is the source's fault"
        );
    }

    /// Where a declaration is read, an operator declaration and an extern
    /// block are keyed by their own features, the keys their unadmitted
    /// readings carry, and any other form as a stray.
    #[test]
    fn a_declaration_position_keys_an_operator_declaration_apart()
    {
        use super::FragmentFeature;

        assert_eq!(
            FragmentFeature::of(
                FormName::OPERATOR_DECLARATION,
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort
            ),
            FragmentFeature::Unbuilt(Unbuilt::OperatorDeclaration),
            "an operator declaration where a declaration is read is its own feature"
        );
        assert_eq!(
            FragmentFeature::of(
                FormName::EXTERN_BLOCK,
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort
            ),
            FragmentFeature::Unbuilt(Unbuilt::ExternBlock),
            "an extern block where a declaration is read is its own feature"
        );
        assert_eq!(
            FragmentFeature::of(
                FormName::HOLD_STATEMENT,
                FragmentSort::Declaration,
                FragmentBoundary::WrongSort
            ),
            FragmentFeature::Stray,
            "any other form where a declaration is read is a stray"
        );
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
        let crossings = [
            FragmentBoundary::Misplaced,
            FragmentBoundary::NotAtResult,
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
        let boundaries: alloc::vec::Vec<FragmentBoundary> = Unbuilt::ALL
            .iter()
            .flat_map(|&feature| {
                [
                    FragmentBoundary::Reserved(feature),
                    FragmentBoundary::Unadmitted(feature),
                ]
            })
            .chain(crossings)
            .collect();
        let mut classes: BTreeMap<FragmentFeature, FailureClass> = BTreeMap::new();
        for &kind in TREE_SITTER_NAMED_KINDS.iter().chain(PBG_ONLY_KINDS) {
            let form = FormName::from(NamedKind(kind));
            for sort in sorts {
                for &boundary in &boundaries {
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
                FailureClass::Unimplemented(TrackingIssue::HIGHER_ORDER_FIELD),
            ),
            (
                MemberFault::DependentField,
                FailureClass::Unimplemented(TrackingIssue::DEPENDENT_FIELD),
            ),
            (
                MemberFault::TypeShape,
                FailureClass::Unimplemented(TrackingIssue::TYPE_SHAPE),
            ),
            (
                MemberFault::NativeDecode,
                FailureClass::Unimplemented(TrackingIssue::NATIVE_DECODE),
            ),
            (
                MemberFault::AggregatedOutput,
                FailureClass::Unimplemented(TrackingIssue::OPERATION_SHAPE),
            ),
            (
                MemberFault::UnrepresentableOperation,
                FailureClass::Unimplemented(TrackingIssue::OPERATION_SHAPE),
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
    fn a_type_eq_generic_does_not_cover_names_its_class_by_its_fault_2302()
    {
        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        let at = gandr_kernel_term::ConstantIndex::from(0_usize);
        let site = gandr_kernel_term::OccurrenceSite::Field {
            tag: gandr_kernel_term::ConstructorTag::from(0_usize),
            field: gandr_kernel_term::FieldPosition::from(0_usize),
        };
        // A type with no structural equality is the author's; one a fuller
        // derivation would cover names its issue; past the ceiling is the
        // engine's.
        let unfinished = FailureClass::Unimplemented(TrackingIssue::GENERIC_EQUALITY);
        let rows = [
            (Uncovered::Unknown(at), FailureClass::MalformedSource),
            (Uncovered::Presented(at), FailureClass::MalformedSource),
            (Uncovered::Field(at, site), FailureClass::MalformedSource),
            (Uncovered::Applied(at), unfinished),
            (Uncovered::Dependent(at, site), unfinished),
            (Uncovered::Cycle(at, site), unfinished),
            (Uncovered::Nested(at, site), unfinished),
            (Uncovered::Inductive(at, site), unfinished),
            (
                Uncovered::DependentCase(at, site),
                FailureClass::Unimplemented(TrackingIssue::CASE_MOTIVE),
            ),
            (
                Uncovered::Uncoded(at, site),
                FailureClass::Unimplemented(TrackingIssue::TYPE_SHAPE),
            ),
            (Uncovered::BinderCeiling, FailureClass::EngineFault),
        ];
        for (fault, class) in rows {
            assert_eq!(
                LoweringRefusal::GenericUncovered {
                    span: empty,
                    data: SurfaceName::from("Shape"),
                    fault,
                }
                .classify(),
                class,
                "a data type refused for {fault:?} carries its pinned class"
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
            "a law at a binding port names its issue"
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
