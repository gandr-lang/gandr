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
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::judged;
use gandr_core_term::ValueTypeId;
use gandr_surface_lowering::OriginTable;
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
        | FrameRole::NativeNext => "checking the next premise of this",
        | FrameRole::NativeYield => "finishing the type of this",
        | FrameRole::NativeCollect => "collecting the field types of this",
        | FrameRole::NativeDiscard => "typing a field of this its expected type does not name",
        | FrameRole::NativeTuple => "synthesising the components of this tuple",
        | FrameRole::NativeRecord => "synthesising the fields of this record",
        | FrameRole::NativeCase => "reading the type of this case's scrutinee",
        | FrameRole::NativeMotive => "forming the motive of this case",
        | FrameRole::NativeProjection => "reading the type this projection selects from",
        | FrameRole::PerformPayload => "checking the payload of this operation",
        | FrameRole::Resume => "reading the stack this resumption resumes",
        | FrameRole::Project => "reading the lazy pair this projection selects from",
        | FrameRole::Reset => "checking the body of this reset",
        | FrameRole::HandlerForm => "forming the interface this handler handles",
        | FrameRole::HandlerSubject => "synthesising the type of this handler's subject",
        | FrameRole::HandlerReturn => "checking the return clause of this handler",
        | FrameRole::HandlerClause => "checking an operation clause of this handler",
        | FrameRole::ExerciseCapability => "synthesising the capability this exercise goes through",
        | FrameRole::ScopeForm => "forming the type the subject of this scope is checked at",
        | FrameRole::ScopeSubject => "checking the subject of this scope under its capability",
        | FrameRole::StackNext => "checking the remaining frames of this stack",
        | FrameRole::StackBind => "checking a bind frame of this stack",
        | FrameRole::ListFold(FoldPremise::Element) => "forming the element type of this fold",
        | FrameRole::ListFold(FoldPremise::Result) => "forming the result type of this fold",
        | FrameRole::ListFold(FoldPremise::Input) => "checking the list this fold folds",
        | FrameRole::ListFold(FoldPremise::Nil) => "checking the empty-list branch of this fold",
        | FrameRole::ListFold(FoldPremise::Cons) => "checking the cell branch of this fold",
        | FrameRole::PathProductFirst => "synthesising the first path of this product",
        | FrameRole::PathProductSecond => "synthesising the second path of this product",
        | FrameRole::PathBackward => "checking the forward map of this path",
        | FrameRole::PathChecked => "checking the backward map of this path",
        | FrameRole::TransportPath => "synthesising the path this transport follows",
        | FrameRole::ElementTransportPath => "synthesising the path this element transport follows",
        | FrameRole::TransportOperand => "checking the operand of this transport",
        | FrameRole::ElementTransportMotive => "forming the motive of this transport",
        | FrameRole::TelescopePath => "synthesising the path this dependent transport follows",
        | FrameRole::TelescopeMotive => "forming the telescope motive of this transport",
        | FrameRole::TelescopeStart => {
            "checking the start of this transport against the family at the path's source"
        },
        | FrameRole::TelescopeOver => {
            "synthesising the identity over the path this transport follows"
        },
        | FrameRole::HereSynthesised => "synthesising the point of this reflexivity",
        | FrameRole::HereEndpoints => {
            "checking the point of this reflexivity against its endpoints"
        },
        | FrameRole::FunextLeft => "synthesising the first function of this extensionality",
        | FrameRole::FunextRight => {
            "checking the second function of this extensionality against the first"
        },
        | FrameRole::EquivForward => "synthesising the forward map of this equivalence",
        | FrameRole::EquivBackward => {
            "checking the backward map of this equivalence against the forward one"
        },
        | FrameRole::UaTranslators => {
            "checking the translators of this univalence against their corollas"
        },
        | FrameRole::SessionStatement => "relating the two protocols of this session statement",
        | FrameRole::StaySynthesised => "synthesising the point of this stay",
        | FrameRole::ThenFirst => "synthesising the first flow of this composite",
        | FrameRole::ThenSecond => {
            "checking the second flow of this composite against the first one's target"
        },
        | FrameRole::RideFlow => "synthesising the flow this ride follows",
        | FrameRole::RideMotive => "forming the motive of this ride",
        | FrameRole::RideValue => "checking the value this ride moves against the flow's source",
        | FrameRole::ForwardTranslator => {
            "deciding this forward flow at every input of its translator"
        },
        | FrameRole::ArrowDomain => "synthesising the domain flow of this arrow",
        | FrameRole::ArrowCodomain => "synthesising the codomain flow of this arrow",
        | FrameRole::ArrowAgainst => {
            "checking this arrow's boundaries against the function codes it relates"
        },
        | FrameRole::StayEndpoints => {
            "meeting the point of this stay with both endpoints of its flow"
        },
        | FrameRole::ReturnedEndpoint => "synthesising the computation of this endpoint",
        | FrameRole::Ran => "synthesising the computation this runs where a value is read",
        | FrameRole::PrimitiveSecond => "checking the first argument of this operation",
        | FrameRole::PrimitiveResult => "checking the arguments of this operation",
        | FrameRole::CaseScrutinee => "synthesising the type of this case's scrutinee",
        | FrameRole::SplitScrutinee => "synthesising the type of this split's scrutinee",
        | FrameRole::SplitBody => "checking the body of this split",
        | FrameRole::CaseBranch => "checking the branches of this case",
        | FrameRole::Next => "checking the remaining parts of this",
        | FrameRole::Force => "forcing this",
        | FrameRole::ApplicationHead => "synthesising the function this applies",
        | FrameRole::ApplicationArgument => "checking the argument of this application",
        | FrameRole::LambdaBody => "checking the body of this function",
        | FrameRole::BindBound => "synthesising the computation this binds",
        | FrameRole::BindBody => "checking the body under this binding",
        | FrameRole::ValueBridge | FrameRole::CompBridge => {
            "comparing the type this synthesises with the one it is checked against"
        },
        | FrameRole::PairSecond => "checking the head of this list cell",
        | FrameRole::Unknowing => "checking this against the unknown type",
        | FrameRole::ThunkBody => "checking the body of this thunk",
        | FrameRole::ReturnValue => "checking the value this returns",
        | FrameRole::InjectionPayload => "checking the payload of this injection",
        | FrameRole::Quote => "forming the type this quotes",
        | FrameRole::FormNext => "forming the parts of this type",
        | FrameRole::FormPi => "forming the domain of this function type",
        | FrameRole::FormBinder => "forming this type under its binder",
        | FrameRole::FormLift => "forming the type this lift raises",
        | FrameRole::FormElement => "synthesising the code this type decodes",
        | FrameRole::FormStaticPi => "forming the classifiers of this type operator",
        | FrameRole::StaticSpine => "synthesising the head of this type operator application",
        | FrameRole::StaticArgument => "synthesising an argument of this type operator application",
        | FrameRole::StaticOperand => "checking an operator argument of this application",
        | FrameRole::FormSession => "forming the payload types of this session type",
        | FrameRole::SessionSend => "checking the payload this sends",
        | FrameRole::OfferArm => "checking an arm of this offer",
        | FrameRole::ForkProtocol => "forming the session type this fork opens",
        | FrameRole::ForkChild => "checking the child this forks",
        | FrameRole::ForkParent => "checking the rest of this fork's parent",
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
/// - witness: `diagnostics::diagnostics::a_refusal_names_the_rules_it_stood_inside`
/// - witness: `diagnostics::diagnostics::a_mismatch_under_a_binder_names_it`
/// - witness: `diagnostics::diagnostics::an_unlocated_rule_becomes_a_note`
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
        let binders: Vec<Binding> = match obligation.at() {
            | CoreNode::Term(TermNode::Computation(opener)) if !obligation.binders().is_empty() => {
                let name = match origins.binder(opener) {
                    | Maybe::Present(origin) => text
                        .fragment(origin.span())
                        .map_or(Maybe::Absent(binding::Absent::Unnamed), |fragment| {
                            Maybe::Present(String::from(fragment.as_ref()))
                        }),
                    | Maybe::Absent(_) => Maybe::Absent(binding::Absent::Unnamed),
                };
                obligation
                    .binders()
                    .iter()
                    .enumerate()
                    .map(|(at, &ty)| Binding {
                        name: if at == 0_usize {
                            name.clone()
                        }
                        else {
                            Maybe::Absent(binding::Absent::Unnamed)
                        },
                        ty: spelled(spellings, ty),
                    })
                    .collect()
            },
            | _ => obligation
                .binders()
                .iter()
                .map(|&ty| Binding {
                    name: Maybe::Absent(binding::Absent::Unnamed),
                    ty: spelled(spellings, ty),
                })
                .collect(),
        };
        named.extend(binders.iter().cloned());
        let judged = match obligation.expected() {
            | Maybe::Present(expected) => Judged::Checked(match spellings.get(expected) {
                | Maybe::Present(presentation) => {
                    Maybe::Present(String::from(presentation.as_ref()))
                },
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            }),
            | Maybe::Absent(judged::Absent::Synthesised) => Judged::Synthesised,
            | Maybe::Absent(judged::Absent::Formed) => Judged::Formed,
        };
        let role = obligation.role();
        let locus = match node(origins, obligation.at()) {
            | Maybe::Present(span) => match Locus::of(text, span) {
                | Maybe::Present(locus) => Maybe::Present(locus),
                | Maybe::Absent(_) => Maybe::Absent(context_locus::Absent::OutsideText),
            },
            | Maybe::Absent(_) => Maybe::Absent(context_locus::Absent::Unrecorded),
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
        | Maybe::Present(presentation) => Maybe::Present(String::from(presentation.as_ref())),
        | Maybe::Absent(reason) => Maybe::Absent(reason),
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
            FrameRole::NativeProjection,
            FrameRole::PerformPayload,
            FrameRole::Next,
            FrameRole::Resume,
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
            FrameRole::SessionStatement,
            FrameRole::StaySynthesised,
            FrameRole::ThenFirst,
            FrameRole::ThenSecond,
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
            FrameRole::Force,
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
            FrameRole::FormBinder,
            FrameRole::FormLift,
            FrameRole::FormElement,
            FrameRole::FormStaticPi,
            FrameRole::PairSecond,
            FrameRole::StaticSpine,
            FrameRole::StaticArgument,
            FrameRole::StaticOperand,
            FrameRole::Unknowing,
            FrameRole::ThunkBody,
            FrameRole::ReturnValue,
            FrameRole::InjectionPayload,
            FrameRole::FormSession,
            FrameRole::SessionSend,
            FrameRole::OfferArm,
            FrameRole::ForkProtocol,
            FrameRole::ForkChild,
            FrameRole::ForkParent,
        ];
        let mut sentences: Vec<super::Sentence> =
            roles.iter().map(|&role| sentence(role)).collect();
        assert!(
            sentences.iter().all(|said| !said.0.is_empty()
                && !said.0.contains('\n')
                && said.0.contains("this"))
        );
        sentences.sort_unstable();
        sentences.dedup();
        assert_eq!(
            sentences.len(),
            roles.len().saturating_sub(1_usize),
            "every rule reads apart from every other, the two bridges alike"
        );
    }
}
