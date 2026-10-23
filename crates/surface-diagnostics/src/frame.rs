//! The sentence each rule of the checking machine reads as, and the contexts a
//! refusal's failure gives a diagnostic.
//!
//! # One sentence per rule, chosen by an exhaustive match
//!
//! Every frame the checking machine keeps on a refusal names its rule as a
//! [`FrameRole`]. [`sentence`] reads each role as what the rule was doing to
//! the term it was pushed for, in the words a user writes: `checking the body
//! of this thunk`, `forcing this`, `checking the argument of this
//! application`. The match names every role and holds no catch-all, so a new
//! frame cannot reach a diagnostic until it says what it does.
//!
//! # A context is one located span, outermost first
//!
//! A refusal's obligations run from the outermost rule to the innermost, each
//! at the node whose judgement pushed it. Several rules can wait on one node —
//! a thunk checked against its type, then its body, say — and the source marks
//! the node once, so [`contexts`] folds the rules at one span into one
//! [`DiagnosticContext`]: its judgement is the outermost one there, which says
//! what the term was checked against or that it synthesised; its role and
//! sentence are the innermost rule's, the one the refusal stood in last; its
//! binders are every binder the rules there opened. A context at the primary
//! span says nothing the primary annotation does not and is left out. A rule
//! whose node the origin table cannot locate — a node the checker minted
//! itself — becomes an unlocated context, kept in order, and two such of one
//! role in a row read as one.
//!
//! The alternative was one context per frame, which marks a span once per rule
//! waiting on it and repeats a bridge beside the term it bridges. Reversal: a
//! face that shows the machine's frames one by one reads the failure's
//! obligations themselves, which the debug verbosity prints.
//!
//! # A binder is named where the source wrote it
//!
//! The checker's hypotheses are types by position; the lowering's origin table
//! records, per lambda a parameter lowered to and per bind a named statement
//! lowered to, where the bound name was written. A context's binders and the
//! diagnostic's hypotheses pair each type with that name when the table holds
//! it, and leave the name absent otherwise: a split, a discarded statement, a
//! lambda the lowering inserted.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CoreNode;
use gandr_core_checker::Failure;
use gandr_core_checker::FoldPremise;
use gandr_core_checker::FrameRole;
use gandr_core_checker::Obligation;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::judged;
use gandr_core_term::ValueTypeId;
use gandr_surface_lowering::ComponentName;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::SplitComponent;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::locus::node;
use crate::model::Binding;
use crate::model::DiagnosticContext;
use crate::model::Judged;
use crate::model::Locus;
use crate::model::binding;
use crate::model::context_locus;
use crate::spelled::Spellings;

/// What a rule of the checking machine was doing to the term it was pushed
/// for, as a clause a context writes after `while`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sentence(&'static str);

impl fmt::Display for Sentence
{
    /// Write the clause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

impl AsRef<str> for Sentence
{
    /// The clause's text.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every role's sentence, read through `as_ref`, is
    ///   compared with the text it displays, so an empty or fixed text shows.
    /// - witness: `frame::tests::every_role_reads_as_a_sentence`
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// What the rule `role` was doing to the term it was pushed for, as a clause
/// a context writes after `while`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one nonempty, single-line sentence per role, every fold premise
///   its own, naming the term as `this` and no core node; distinct roles of
///   distinct rules read as distinct sentences, except the two bridges, which
///   compare alike.
/// - provides: the sentence of every context.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every role, fold premises included, reads as a nonempty
///   single-line sentence mentioning `this`.
/// - witness: `frame::tests::every_role_reads_as_a_sentence`
#[spec(ensures: |ret| !ret.0.is_empty() && !ret.0.contains('\n') && ret.0.contains("this"))]
#[inline]
#[must_use]
pub fn sentence(role: FrameRole) -> Sentence
{
    Sentence(match role {
        FrameRole::NativeNext => "checking the next premise of this",
        FrameRole::NativeYield => "finishing the type of this",
        FrameRole::NativeCollect => "collecting the field types of this",
        FrameRole::NativeDiscard => "typing a field of this its expected type does not name",
        FrameRole::NativeTuple => "synthesising the components of this tuple",
        FrameRole::NativeRecord => "synthesising the fields of this record",
        FrameRole::NativeCase => "reading the type of this case's scrutinee",
        FrameRole::NativeMotive => "forming the motive of this case",
        FrameRole::NativeRespect => "showing this case respects its datatype's rules",
        FrameRole::NativeLoops => "showing this case respects its sort's loops",
        FrameRole::SigmaSplitScrutinee => "reading the dependent record this match splits",
        FrameRole::SigmaSplitMotive => "forming the motive of this dependent match",
        FrameRole::NativeProjection => "reading the type this projection selects from",
        FrameRole::Ascription => "checking this computation against the type it is ascribed",
        FrameRole::PerformPayload => "checking the payload of this operation",
        FrameRole::Resume => "reading the stack this resumption resumes",
        FrameRole::Abandon => "reading the stack this abandonment ends",
        FrameRole::Project => "reading the lazy product this projection selects from",
        FrameRole::Reset => "checking the body of this reset",
        FrameRole::HandlerForm => "forming the interface this handler handles",
        FrameRole::HandlerSubject => "synthesising the type of this handler's subject",
        FrameRole::HandlerReturn => "checking the return clause of this handler",
        FrameRole::HandlerClause => "checking an operation clause of this handler",
        FrameRole::ExerciseCapability => "synthesising the capability this exercise goes through",
        FrameRole::ScopeForm => "forming the type the subject of this scope is checked at",
        FrameRole::ScopeSubject => "checking the subject of this scope under its capability",
        FrameRole::StackNext => "checking the remaining frames of this stack",
        FrameRole::StackBind => "checking a bind frame of this stack",
        FrameRole::ListFold(FoldPremise::Element) => "forming the element type of this fold",
        FrameRole::ListFold(FoldPremise::Result) => "forming the result type of this fold",
        FrameRole::ListFold(FoldPremise::Input) => "checking the list this fold folds",
        FrameRole::ListFold(FoldPremise::Nil) => "checking the empty-list branch of this fold",
        FrameRole::ListFold(FoldPremise::Cons) => "checking the cell branch of this fold",
        FrameRole::PathProductFirst => "synthesising the first path of this product",
        FrameRole::PathProductSecond => "synthesising the second path of this product",
        FrameRole::PathBackward => "checking the forward map of this path",
        FrameRole::PathChecked => "checking the backward map of this path",
        FrameRole::TransportPath => "synthesising the path this transport follows",
        FrameRole::ElementTransportPath => "synthesising the path this element transport follows",
        FrameRole::TransportOperand => "checking the operand of this transport",
        FrameRole::ElementTransportMotive => "forming the motive of this transport",
        FrameRole::TelescopePath => "synthesising the path this dependent transport follows",
        FrameRole::TelescopeMotive => "forming the telescope motive of this transport",
        FrameRole::TelescopeStart => {
            "checking the start of this transport against the family at the path's source"
        },
        FrameRole::TelescopeOver => {
            "synthesising the identity over the path this transport follows"
        },
        FrameRole::HereSynthesised => "synthesising the point of this reflexivity",
        FrameRole::HereEndpoints => "checking the point of this reflexivity against its endpoints",
        FrameRole::FunextLeft => "synthesising the first function of this extensionality",
        FrameRole::FunextRight => {
            "checking the second function of this extensionality against the first"
        },
        FrameRole::EquivForward => "synthesising the forward map of this equivalence",
        FrameRole::EquivBackward => {
            "checking the backward map of this equivalence against the forward one"
        },
        FrameRole::UaTranslators => {
            "checking the translators of this univalence against their corollas"
        },
        FrameRole::UnivalenceRecord => "synthesising the record of this univalence",
        FrameRole::UnivalenceChecked => {
            "checking the record of this univalence and the codes it relates"
        },
        FrameRole::SessionStatement => "relating the two protocols of this session statement",
        FrameRole::SessionPayloads => "checking the payload paths of this session equivalence",
        FrameRole::StaySynthesised => "synthesising the point of this stay",
        FrameRole::ThenFirst => "synthesising the first flow of this composite",
        FrameRole::ThenSecond => {
            "checking the second flow of this composite against the first one's target"
        },
        FrameRole::FlowProductFirst => "synthesising the first flow of this product",
        FrameRole::FlowProductSecond => "synthesising the second flow of this product",
        FrameRole::RideFlow => "synthesising the flow this ride follows",
        FrameRole::RideMotive => "forming the motive of this ride",
        FrameRole::RideValue => "checking the value this ride moves against the flow's source",
        FrameRole::ForwardTranslator => {
            "deciding this forward flow at every input of its translator"
        },
        FrameRole::ArrowDomain => "synthesising the domain flow of this arrow",
        FrameRole::ArrowCodomain => "synthesising the codomain flow of this arrow",
        FrameRole::ArrowAgainst => {
            "checking this arrow's boundaries against the function codes it relates"
        },
        FrameRole::StayEndpoints => {
            "meeting the point of this stay with both endpoints of its flow"
        },
        FrameRole::ReturnedEndpoint => "synthesising the computation of this endpoint",
        FrameRole::Ran => "synthesising the computation this runs where a value is read",
        FrameRole::PrimitiveSecond => "checking the first argument of this operation",
        FrameRole::PrimitiveResult => "checking the arguments of this operation",
        FrameRole::CaseScrutinee => "synthesising the type of this case's scrutinee",
        FrameRole::SplitScrutinee => "synthesising the type of this split's scrutinee",
        FrameRole::SplitBody => "checking the body of this split",
        FrameRole::CaseBranch => "checking the branches of this case",
        FrameRole::ListCaseScrutinee => "synthesising the type of the list this case reads",
        FrameRole::ListCaseNil => "checking the empty branch of this list case",
        FrameRole::ListCaseCons => "checking the cell branch of this list case",
        FrameRole::FixpointArgument => "synthesising the argument this recursion starts from",
        FrameRole::Next => "checking the remaining parts of this",
        FrameRole::Force => "forcing this",
        FrameRole::Decompose => "decomposing this dialogue",
        FrameRole::ApplicationHead => "synthesising the function this applies",
        FrameRole::ApplicationArgument => "checking the argument of this application",
        FrameRole::LambdaBody => "checking the body of this function",
        FrameRole::BindBound => "synthesising the computation this binds",
        FrameRole::BindBody => "checking the body under this binding",
        FrameRole::ValueBridge | FrameRole::CompBridge => {
            "comparing the type this synthesises with the one it is checked against"
        },
        FrameRole::PairSecond => "checking the first part of this list cell or dependent record",
        FrameRole::Unknowing => "checking this against the unknown type",
        FrameRole::ThunkBody => "checking the body of this thunk",
        FrameRole::ReturnValue => "judging the value this returns",
        FrameRole::InjectionPayload => "checking the payload of this injection",
        FrameRole::Quote => "forming the type this quotes",
        FrameRole::FormNext => "forming the parts of this type",
        FrameRole::FormPi => "forming the domain of this function type",
        FrameRole::FormSigma => "forming the first entry of this dependent record",
        FrameRole::FormBinder => "forming this type under its binder",
        FrameRole::FormLift => "forming the type this lift raises",
        FrameRole::FormElement => "synthesising the code this type decodes",
        FrameRole::FormStaticPi => "forming the classifiers of this type operator",
        FrameRole::RunProtocol => "checking the protocol of this run type",
        FrameRole::StaticSpine => "synthesising the head of this type operator application",
        FrameRole::StaticArgument => "synthesising an argument of this type operator application",
        FrameRole::StaticOperand => "checking an operator argument of this application",
        FrameRole::SessionSend => "checking the payload this sends",
        FrameRole::ReceiveBody => "checking the rest of this receive's block",
        FrameRole::OfferArm => "checking an arm of this offer",
        FrameRole::ForkProtocol => "forming the session type this fork opens",
        FrameRole::ForkChild => "checking the child this forks",
        FrameRole::ForkParent => "checking the rest of this fork's parent",
        FrameRole::HoldValue => "synthesising the value this holds",
        FrameRole::HoldBody => "checking the scope of this hold",
        FrameRole::AccessIndex => "checking the index of this access",
        FrameRole::AccessBody => "checking the body of this access",
        FrameRole::AccessUnwind => "checking the unwind of this access under the empty row",
        FrameRole::ResumeValue => "checking the value this resume writes back",
        FrameRole::WorldHold => "synthesising the value this holds at its world",
        FrameRole::LetaValue => "synthesising the handle this opens",
        FrameRole::LetaBody => "checking the rest under the value this opens",
        FrameRole::MigrateBody => "checking the body of this migration at its world",
    })
}

/// The contexts `failure` gives a diagnostic whose primary annotation spans
/// `primary`, and the hypotheses in scope where it was refused, read through
/// `origins`, `spellings` and `text`.
///
/// # Specification
/// - requires: `origins` and `spellings` were built over the arena `failure`
///   names; `text` is the source `origins` measures.
/// - ensures: the obligations in order, outermost first, folded as the module
///   states: one located context per span the text holds, at its first
///   obligation's place, judged as its outermost obligation there and read as
///   its innermost, with every binder opened there; none at `primary`; an
///   obligation the table or the text cannot locate is an unlocated context,
///   one per run of equal roles. The hypotheses are the failure's, each named
///   where its binder's name was written when the obligations account for every
///   hypothesis.
/// - provides: what a diagnostic says the refusal stood inside.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a force inside a thunk reads as the thunk checked against
///   its type while checking its body, with the force at the primary span left
///   out; a mismatch under a `run` binder names the binder; a refusal inside a
///   checker-minted node keeps an unlocated context.
/// - witness: `tests::diagnostics::a_refusal_names_the_rules_it_stood_inside`
/// - witness: `tests::diagnostics::a_mismatch_under_a_binder_names_it`
/// - witness: `tests::diagnostics::an_unlocated_rule_becomes_a_note`
#[spec(ensures: |ret| ret.0.iter().all(|context| match context.locus {
    Maybe::Present(locus) => primary != Maybe::Present(locus.span),
    Maybe::Absent(_) => true,
}) && ret.1.len() == failure.hypotheses().len())]
pub fn contexts<Reason>(
    failure: &Failure,
    origins: &OriginTable,
    spellings: &Spellings,
    text: SourceText<'_>,
    primary: Maybe<ByteSpan, Reason>,
) -> (Vec<DiagnosticContext>, Vec<Binding>)
where
    Reason: Copy + PartialEq,
{
    let mut contexts: Vec<DiagnosticContext> = Vec::new();
    let mut named: Vec<Binding> = Vec::with_capacity(failure.hypotheses().len());
    for obligation in failure.obligations() {
        let binders: Vec<Binding> = opened(obligation, origins, text)
            .into_iter()
            .zip(obligation.binders())
            .map(|(name, &ty)| Binding {
                name,
                ty: spelled(spellings, ty),
            })
            .collect();
        named.extend(binders.iter().cloned());
        let judged = match obligation.expected() {
            Maybe::Present(expected) => Judged::Checked(match spellings.get(expected) {
                Maybe::Present(presentation) => Maybe::Present(String::from(presentation.as_ref())),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            }),
            Maybe::Absent(judged::Absent::Synthesised) => Judged::Synthesised,
            Maybe::Absent(judged::Absent::Formed) => Judged::Formed,
        };
        let role = obligation.role();
        let locus = match node(origins, obligation.at()) {
            Maybe::Present(span) => match Locus::of(text, span) {
                Maybe::Present(locus) => Maybe::Present(locus),
                Maybe::Absent(_) => Maybe::Absent(context_locus::Absent::OutsideText),
            },
            Maybe::Absent(_) => Maybe::Absent(context_locus::Absent::Unrecorded),
        };
        if let Maybe::Present(locus) = locus {
            if let Maybe::Present(span) = primary
                && span == locus.span
            {
                continue;
            }
            if let Some(held) = contexts.iter_mut().find(
                |held| matches!(held.locus, Maybe::Present(other) if other.span == locus.span),
            ) {
                held.role = role;
                held.sentence = sentence(role);
                held.binders.extend(binders);
                continue;
            }
        }
        else if let Some(last) = contexts.last_mut()
            && matches!(last.locus, Maybe::Absent(_))
            && last.role == role
        {
            last.binders.extend(binders);
            continue;
        }
        contexts.push(DiagnosticContext {
            role,
            sentence: sentence(role),
            judged,
            binders,
            locus,
        });
    }
    let hypotheses = if named.len() == failure.hypotheses().len() {
        named
    }
    else {
        failure
            .hypotheses()
            .iter()
            .map(|&ty| Binding {
                name: Maybe::Absent(binding::Absent::Unnamed),
                ty: spelled(spellings, ty),
            })
            .collect()
    };
    (contexts, hypotheses)
}

/// The names of the binders `obligation` opens, outermost first, read through
/// `origins` and `text`.
///
/// # Specification
/// - requires: `origins` was built over the arena `obligation` names; `text` is
///   the source `origins` measures.
/// - ensures: one name per binder the obligation opens: the first binder of a
///   computation opener the table records a binder for is named by the bytes
///   the table locates; a binder of a split the table records a component for
///   is named by the pattern variable written for it, or by the label of the
///   field a labelled pattern leaves unwritten; every other binder is
///   [`binding::Absent::Unnamed`].
/// - provides: the names a context's binders, the diagnostic's hypotheses and
///   the spelling of every type under them read ([`crate::TypeSpellings::of`]).
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `run` binder and a function's parameters are named, and
///   a type over them spells them by those names; a record split's two binders,
///   the second's type naming the first, are named as the pattern writes them.
/// - witness: `tests::diagnostics::a_mismatch_under_a_binder_names_it`
/// - witness: `tests::diagnostics::a_refusal_spells_its_binders_by_name_418`
/// - witness: `tests::diagnostics::a_later_binder_of_one_split_spells_under_the_earlier`
#[spec(ensures: |ret| ret.len() == obligation.binders().len())]
pub fn opened(
    obligation: &Obligation,
    origins: &OriginTable,
    text: SourceText<'_>,
) -> Vec<Maybe<String, binding::Absent>>
{
    let name = written_binder(obligation.at(), origins, text);
    (0_usize .. obligation.binders().len())
        .map(|at| match name {
            Maybe::Present(ref name) if at == 0_usize => Maybe::Present(name.clone()),
            Maybe::Present(_) | Maybe::Absent(_) => {
                split_binder(obligation.at(), SplitComponent::from(at), origins, text)
            },
        })
        .collect()
}

/// The name the source writes for the binder at `component` of the split at
/// `at`, read through `origins` and `text`.
///
/// # Specification
/// - requires: as [`opened`].
/// - ensures: for a split the table records the component for, the pattern
///   variable's bytes, or the label a labelled pattern leaves unwritten;
///   [`binding::Absent::Unnamed`] for every other node and component.
/// - provides: the split's binders [`opened`] names.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`opened`].
/// - witness: `tests::diagnostics::a_later_binder_of_one_split_spells_under_the_earlier`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_))
    || matches!(at, CoreNode::Term(TermNode::Computation(_))))]
fn split_binder(
    at: CoreNode,
    component: SplitComponent,
    origins: &OriginTable,
    text: SourceText<'_>,
) -> Maybe<String, binding::Absent>
{
    let CoreNode::Term(TermNode::Computation(split)) = at
    else {
        return Maybe::Absent(binding::Absent::Unnamed);
    };
    match origins.component(split, component) {
        Maybe::Present(&ComponentName::Written(origin)) => text
            .fragment(origin.span())
            .map_or(Maybe::Absent(binding::Absent::Unnamed), |fragment| {
                Maybe::Present(String::from(fragment.as_ref()))
            }),
        Maybe::Present(&ComponentName::Labelled(ref label)) => {
            Maybe::Present(String::from(label.as_ref()))
        },
        Maybe::Absent(_) => Maybe::Absent(binding::Absent::Unnamed),
    }
}

/// The name the source writes for the first binder the former at `at` opens,
/// read through `origins` and `text`: a `run`'s binder, a function's first
/// parameter, a scope's capability, a hold's slot.
///
/// # Specification
/// - requires: as [`opened`].
/// - ensures: for a computation opener the table records a binder for, the
///   bytes the table locates; [`binding::Absent::Unnamed`] for every other
///   node.
/// - provides: the name of a binder [`opened`] reads and of a region a failure
///   stood in ([`crate::TypeSpellings::of`]), whether the binder is among the
///   hypotheses or, a hold's slot, linear.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`opened`]; a type kept at a hold spells the hold's
///   slot.
/// - witness: `tests::diagnostics::a_refusal_spells_its_binders_by_name_418`
/// - witness: `tests::diagnostics::a_trace_spells_a_kept_region_by_its_name_1494`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_))
    || matches!(at, CoreNode::Term(TermNode::Computation(_))))]
pub fn written_binder(
    at: CoreNode,
    origins: &OriginTable,
    text: SourceText<'_>,
) -> Maybe<String, binding::Absent>
{
    match at {
        CoreNode::Term(TermNode::Computation(opener)) => match origins.binder(opener) {
            Maybe::Present(origin) => text
                .fragment(origin.span())
                .map_or(Maybe::Absent(binding::Absent::Unnamed), |fragment| {
                    Maybe::Present(String::from(fragment.as_ref()))
                }),
            Maybe::Absent(_) => Maybe::Absent(binding::Absent::Unnamed),
        },
        CoreNode::Term(_) | CoreNode::Type(_) => Maybe::Absent(binding::Absent::Unnamed),
    }
}

/// The spelling of the value type `ty`.
///
/// # Specification
/// trivial.
fn spelled(
    spellings: &Spellings,
    ty: ValueTypeId,
) -> Maybe<String, crate::spelled::spelling::Absent>
{
    match spellings.get(TypeNode::Value(ty)) {
        Maybe::Present(presentation) => Maybe::Present(String::from(presentation.as_ref())),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::FoldPremise;
    use gandr_core_checker::FrameRole;

    use super::sentence;

    #[test]
    fn every_role_reads_as_a_sentence()
    {
        let roles = [
            FrameRole::NativeNext,
            FrameRole::NativeYield,
            FrameRole::NativeCollect,
            FrameRole::NativeDiscard,
            FrameRole::NativeTuple,
            FrameRole::NativeRecord,
            FrameRole::NativeCase,
            FrameRole::NativeMotive,
            FrameRole::NativeRespect,
            FrameRole::NativeLoops,
            FrameRole::SigmaSplitScrutinee,
            FrameRole::SigmaSplitMotive,
            FrameRole::NativeProjection,
            FrameRole::Ascription,
            FrameRole::PerformPayload,
            FrameRole::Next,
            FrameRole::Resume,
            FrameRole::Abandon,
            FrameRole::Project,
            FrameRole::Reset,
            FrameRole::HandlerForm,
            FrameRole::HandlerSubject,
            FrameRole::HandlerReturn,
            FrameRole::HandlerClause,
            FrameRole::ExerciseCapability,
            FrameRole::ScopeForm,
            FrameRole::ScopeSubject,
            FrameRole::StackNext,
            FrameRole::StackBind,
            FrameRole::ListFold(FoldPremise::Element),
            FrameRole::ListFold(FoldPremise::Result),
            FrameRole::ListFold(FoldPremise::Input),
            FrameRole::ListFold(FoldPremise::Nil),
            FrameRole::ListFold(FoldPremise::Cons),
            FrameRole::PathProductFirst,
            FrameRole::PathProductSecond,
            FrameRole::PathBackward,
            FrameRole::PathChecked,
            FrameRole::PrimitiveSecond,
            FrameRole::PrimitiveResult,
            FrameRole::TransportPath,
            FrameRole::TransportOperand,
            FrameRole::HereSynthesised,
            FrameRole::HereEndpoints,
            FrameRole::FunextLeft,
            FrameRole::FunextRight,
            FrameRole::EquivForward,
            FrameRole::EquivBackward,
            FrameRole::UaTranslators,
            FrameRole::UnivalenceRecord,
            FrameRole::UnivalenceChecked,
            FrameRole::SessionStatement,
            FrameRole::SessionPayloads,
            FrameRole::StaySynthesised,
            FrameRole::ThenFirst,
            FrameRole::ThenSecond,
            FrameRole::FlowProductFirst,
            FrameRole::FlowProductSecond,
            FrameRole::RideFlow,
            FrameRole::RideMotive,
            FrameRole::RideValue,
            FrameRole::ForwardTranslator,
            FrameRole::ArrowDomain,
            FrameRole::ArrowCodomain,
            FrameRole::ArrowAgainst,
            FrameRole::StayEndpoints,
            FrameRole::ReturnedEndpoint,
            FrameRole::Ran,
            FrameRole::ElementTransportPath,
            FrameRole::ElementTransportMotive,
            FrameRole::TelescopePath,
            FrameRole::TelescopeMotive,
            FrameRole::TelescopeStart,
            FrameRole::TelescopeOver,
            FrameRole::CaseScrutinee,
            FrameRole::SplitScrutinee,
            FrameRole::SplitBody,
            FrameRole::CaseBranch,
            FrameRole::ListCaseScrutinee,
            FrameRole::ListCaseNil,
            FrameRole::ListCaseCons,
            FrameRole::FixpointArgument,
            FrameRole::Force,
            FrameRole::Decompose,
            FrameRole::ApplicationHead,
            FrameRole::ApplicationArgument,
            FrameRole::LambdaBody,
            FrameRole::BindBound,
            FrameRole::BindBody,
            FrameRole::ValueBridge,
            FrameRole::CompBridge,
            FrameRole::Quote,
            FrameRole::FormNext,
            FrameRole::FormPi,
            FrameRole::FormSigma,
            FrameRole::FormBinder,
            FrameRole::FormLift,
            FrameRole::FormElement,
            FrameRole::FormStaticPi,
            FrameRole::RunProtocol,
            FrameRole::PairSecond,
            FrameRole::StaticSpine,
            FrameRole::StaticArgument,
            FrameRole::StaticOperand,
            FrameRole::Unknowing,
            FrameRole::ThunkBody,
            FrameRole::ReturnValue,
            FrameRole::InjectionPayload,
            FrameRole::SessionSend,
            FrameRole::ReceiveBody,
            FrameRole::OfferArm,
            FrameRole::ForkProtocol,
            FrameRole::ForkChild,
            FrameRole::ForkParent,
            FrameRole::HoldValue,
            FrameRole::HoldBody,
            FrameRole::AccessIndex,
            FrameRole::AccessBody,
            FrameRole::AccessUnwind,
            FrameRole::ResumeValue,
            FrameRole::WorldHold,
            FrameRole::LetaValue,
            FrameRole::LetaBody,
            FrameRole::MigrateBody,
        ];
        let mut sentences: Vec<super::Sentence> =
            roles.iter().map(|&role| sentence(role)).collect();
        let mut written = String::new();
        assert!(sentences.iter().all(|said| {
            let text: &str = said.as_ref();
            written.clear();
            core::fmt::Write::write_fmt(&mut written, format_args!("{said}"))
                .expect("a sentence writes");
            text == written && !text.is_empty() && !text.contains('\n') && text.contains("this")
        }));
        sentences.sort_unstable();
        sentences.dedup();
        assert_eq!(
            sentences.len(),
            roles.len().saturating_sub(1_usize),
            "every rule reads apart from every other, the two bridges alike"
        );
    }
}
