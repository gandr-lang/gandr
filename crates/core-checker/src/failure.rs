//! What a refused run leaves behind: the refusal, the obligations still
//! pending, the goal under way and the hypotheses in scope.
//!
//! # The machine's own state is the failure
//!
//! The judgement's machine keeps a stack of frames, one per rule waiting on a
//! subterm, and each frame remembers the goal whose rule pushed it. When a rule
//! refuses, the run hands that stack back as a [`Failure`] instead of dropping
//! it: one [`Obligation`] per frame, outermost first, each naming its
//! [`FrameRole`], the node its rule stands on and the type that node was
//! checked against; the [`Pursuit`] the machine was making when the refusal
//! came; and the hypotheses the run had opened, each beside the obligation that
//! opened it. A frame whose rule refused while consuming its subterm's result
//! stays on the stack as the innermost obligation, so the rule that refused is
//! named as well as the subterm it refused.
//!
//! The strict faces ([`check_value`], [`synthesise_value`] and the rest)
//! project the refusal out of the failure; [`check_module`] keeps each refused
//! body's failure in its report, so a face builds nested reasons from the run
//! that refused, not from a second run.
//!
//! **Choice.** One run, its frames returned on refusal. **Alternative.** A
//! traced re-run of each refused body, recording the term judgements the
//! refusal stood inside: it doubles the work on every refused body and names
//! the terms but not the rules that waited on them. **Reversal.** A consumer
//! that needs the state of an accepted run — a type for every node, say —
//! records it during the run rather than from the failure.
//!
//! # A frame is located by the goal that pushed it
//!
//! Most frames carry no node of their own: a lambda's body frame holds nothing,
//! an application's head frame holds its head and argument but not itself. The
//! machine pairs each frame with the goal under way when its rule pushed it, so
//! every obligation names the term or type its rule stands on. The arena mints
//! a fresh node for every term the producer writes, so two equal terms in two
//! places are two nodes, and an obligation names exactly one occurrence.
//!
//! [`check_value`]: crate::check_value
//! [`synthesise_value`]: crate::synthesise_value
//! [`check_module`]: crate::check_module

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;

quenchant_shape::reason_enum! {
    /// Why a judgement names no type it was checked against.
    pub mod judged {
        /// The reason the expected type is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement synthesised its term's type.
            Synthesised,
            /// The judgement formed a type, which is checked against nothing.
            Formed,
        }
    }
}

/// The premise of a List fold that a fold frame awaits.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FoldPremise
{
    /// The element annotation is being formed.
    Element,
    /// The result annotation is being formed.
    Result,
    /// The folded list is being checked at the element type.
    Input,
    /// The nil branch is being checked.
    Nil,
    /// The cell branch is being checked under its two binders.
    Cons,
}

/// The rule a pending frame stands for, one per frame of the machine.
///
/// Its `Display` writes the role's stable name, the frame's own name, which a
/// tool may match on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FrameRole
{
    /// A later premise of a native rule waits for the one under way.
    NativeNext,
    /// A native rule waits to hand out its result once its premises are done.
    NativeYield,
    /// A native rule collects a synthesised field type.
    NativeCollect,
    /// A record field the expected type does not name is being typed.
    NativeDiscard,
    /// A synthesised tuple waits on its components' types.
    NativeTuple,
    /// A synthesised record waits on its fields' types.
    NativeRecord,
    /// A data case waits on its scrutinee's type.
    NativeCase,
    /// A data case waits on its motive's formation.
    NativeMotive,
    /// A projection waits on its operand's type.
    NativeProjection,
    /// An operation request waits on its interface's formation.
    PerformPayload,
    /// A later premise waits for the one under way.
    Next,
    /// A resumption waits on its stack's type.
    Resume,
    /// A lazy-pair projection waits on its subject's type.
    Project,
    /// A reset's body is being checked against its answer type.
    Reset,
    /// A handler waits on its interface's formation.
    HandlerForm,
    /// A handler waits on its subject's type.
    HandlerSubject,
    /// A handler's return clause is being checked.
    HandlerReturn,
    /// One of a handler's operation clauses is being checked.
    HandlerClause,
    /// A stack literal waits on one of its frames.
    StackNext,
    /// A stack literal's bind frame waits on its body's type.
    StackBind,
    /// A List fold waits on one of its premises.
    ListFold(FoldPremise),
    /// A path product waits on its first path's type.
    PathProductFirst,
    /// A path product waits on its second path's type.
    PathProductSecond,
    /// A path's forward map is being checked.
    PathBackward,
    /// A path's backward map is being checked.
    PathChecked,
    /// A native operation's first argument is being checked.
    PrimitiveSecond,
    /// A native operation's arguments are being checked.
    PrimitiveResult,
    /// A transport waits on its path's type.
    TransportPath,
    /// A transport's operand is being checked.
    TransportOperand,
    /// A reflexivity waits on its point's type.
    HereSynthesised,
    /// A reflexivity's point is being checked against the carrier.
    HereEndpoints,
    /// A function extensionality waits on its first function's type.
    FunextLeft,
    /// A function extensionality's second function is being checked against
    /// the first's type.
    FunextRight,
    /// A universe equivalence waits on its forward translator's type.
    EquivForward,
    /// A universe equivalence's backward translator is being checked against
    /// the inverse of the forward's type.
    EquivBackward,
    /// A compound endpoint waits on its computation's type.
    ReturnedEndpoint,
    /// A transport waits on its element path's type.
    ElementTransportPath,
    /// A transport waits on its motive's formation.
    ElementTransportMotive,
    /// A case waits on its scrutinee's type.
    CaseScrutinee,
    /// A split waits on its scrutinee's type.
    SplitScrutinee,
    /// A split's body is being checked under its binders.
    SplitBody,
    /// A later branch of a case waits for the one under way.
    CaseBranch,
    /// A force waits on its value's type.
    Force,
    /// An application waits on its head's type.
    ApplicationHead,
    /// An application's argument is being checked.
    ApplicationArgument,
    /// A body is being checked under the binder its abstraction opened.
    LambdaBody,
    /// A bind waits on its bound computation's type.
    BindBound,
    /// A bind's body is being judged under the binder it opened.
    BindBody,
    /// A synthesising value in checking position waits on its type.
    ValueBridge,
    /// A synthesising computation in checking position waits on its type.
    CompBridge,
    /// A quote waits on the formation of the type it quotes.
    Quote,
    /// A later child of a type former waits for the one under way.
    FormNext,
    /// A dependent arrow waits on its domain's formation.
    FormPi,
    /// A type is being formed under the binder its former opened.
    FormBinder,
    /// A lift waits on its type's formation.
    FormLift,
    /// A decode waits on its code's type.
    FormElement,
    /// A static Pi waits on its classifiers' formation.
    FormStaticPi,
    /// A list cell's head is being checked.
    PairSecond,
    /// A static application waits on its head's type.
    StaticSpine,
    /// A static application's argument waits on its type.
    StaticArgument,
    /// A static application's operator argument is being checked.
    StaticOperand,
    /// A term that cannot synthesise is being checked against the unknown
    /// type.
    Unknowing,
    /// A thunk's body is being checked.
    ThunkBody,
    /// A return's value is being checked.
    ReturnValue,
    /// An injection's payload is being checked.
    InjectionPayload,
}

impl fmt::Display for FrameRole
{
    /// Writes the role's stable name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the frame's own name, `ListFold` for every fold
    ///   premise; distinct roles of distinct frames write distinct names.
    /// - provides: the name a tool matches a context's role by.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every role writes a nonempty name and no two frames'
    ///   roles share one.
    /// - witness: `failure::tests::every_role_has_its_own_name`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::NativeNext => "NativeNext",
            | Self::NativeYield => "NativeYield",
            | Self::NativeCollect => "NativeCollect",
            | Self::NativeDiscard => "NativeDiscard",
            | Self::NativeTuple => "NativeTuple",
            | Self::NativeRecord => "NativeRecord",
            | Self::NativeCase => "NativeCase",
            | Self::NativeMotive => "NativeMotive",
            | Self::NativeProjection => "NativeProjection",
            | Self::PerformPayload => "PerformPayload",
            | Self::Next => "Next",
            | Self::Resume => "Resume",
            | Self::Project => "Project",
            | Self::Reset => "Reset",
            | Self::HandlerForm => "HandlerForm",
            | Self::HandlerSubject => "HandlerSubject",
            | Self::HandlerReturn => "HandlerReturn",
            | Self::HandlerClause => "HandlerClause",
            | Self::StackNext => "StackNext",
            | Self::StackBind => "StackBind",
            | Self::ListFold(_) => "ListFold",
            | Self::PathProductFirst => "PathProductFirst",
            | Self::PathProductSecond => "PathProductSecond",
            | Self::PathBackward => "PathBackward",
            | Self::PathChecked => "PathChecked",
            | Self::PrimitiveSecond => "PrimitiveSecond",
            | Self::PrimitiveResult => "PrimitiveResult",
            | Self::TransportPath => "TransportPath",
            | Self::TransportOperand => "TransportOperand",
            | Self::HereSynthesised => "HereSynthesised",
            | Self::HereEndpoints => "HereEndpoints",
            | Self::FunextLeft => "FunextLeft",
            | Self::FunextRight => "FunextRight",
            | Self::EquivForward => "EquivForward",
            | Self::EquivBackward => "EquivBackward",
            | Self::ReturnedEndpoint => "ReturnedEndpoint",
            | Self::ElementTransportPath => "ElementTransportPath",
            | Self::ElementTransportMotive => "ElementTransportMotive",
            | Self::CaseScrutinee => "CaseScrutinee",
            | Self::SplitScrutinee => "SplitScrutinee",
            | Self::SplitBody => "SplitBody",
            | Self::CaseBranch => "CaseBranch",
            | Self::Force => "Force",
            | Self::ApplicationHead => "ApplicationHead",
            | Self::ApplicationArgument => "ApplicationArgument",
            | Self::LambdaBody => "LambdaBody",
            | Self::BindBound => "BindBound",
            | Self::BindBody => "BindBody",
            | Self::ValueBridge => "ValueBridge",
            | Self::CompBridge => "CompBridge",
            | Self::Quote => "Quote",
            | Self::FormNext => "FormNext",
            | Self::FormPi => "FormPi",
            | Self::FormBinder => "FormBinder",
            | Self::FormLift => "FormLift",
            | Self::FormElement => "FormElement",
            | Self::FormStaticPi => "FormStaticPi",
            | Self::PairSecond => "PairSecond",
            | Self::StaticSpine => "StaticSpine",
            | Self::StaticArgument => "StaticArgument",
            | Self::StaticOperand => "StaticOperand",
            | Self::Unknowing => "Unknowing",
            | Self::ThunkBody => "ThunkBody",
            | Self::ReturnValue => "ReturnValue",
            | Self::InjectionPayload => "InjectionPayload",
        })
    }
}

/// One rule pending when a run refused: a frame of the machine.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Obligation
{
    /// The rule the frame stands for.
    role: FrameRole,
    /// The node the rule stands on: the goal under way when it pushed the
    /// frame.
    at: CoreNode,
    /// The type that node was checked against.
    expected: Maybe<TypeNode, judged::Absent>,
    /// The types of the binders the rule opened and has not closed, outermost
    /// first.
    binders: Vec<ValueTypeId>,
}

impl Obligation
{
    /// The obligation of a frame of `role`, pushed while `at` was judged
    /// against `expected`, holding the binders of types `binders` open.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        role: FrameRole,
        at: CoreNode,
        expected: Maybe<TypeNode, judged::Absent>,
        binders: Vec<ValueTypeId>,
    ) -> Self
    {
        Self {
            role,
            at,
            expected,
            binders,
        }
    }

    /// The rule the frame stands for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn role(&self) -> FrameRole
    {
        self.role
    }

    /// The node the rule stands on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(&self) -> CoreNode
    {
        self.at
    }

    /// The type the node the rule stands on was checked against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn expected(&self) -> Maybe<TypeNode, judged::Absent>
    {
        self.expected
    }

    /// The types of the binders the rule holds open, outermost first; empty
    /// for a rule that opens none, and for every rule when the run's binders
    /// could not be attributed to its frames.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binders(&self) -> &[ValueTypeId]
    {
        &self.binders
    }
}

/// Where the machine stood when its run refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage
{
    /// It was starting the goal under way.
    Starting,
    /// The innermost obligation's rule was consuming its subterm's result.
    Resuming,
    /// It was handing a finished result to the innermost obligation.
    Handing,
}

/// The goal a run was pursuing when it refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pursuit
{
    /// The node judged or formed.
    at: CoreNode,
    /// The type it was checked against.
    expected: Maybe<TypeNode, judged::Absent>,
    /// Where the machine stood.
    stage: Stage,
}

impl Pursuit
{
    /// The pursuit of `at` against `expected`, at `stage`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        at: CoreNode,
        expected: Maybe<TypeNode, judged::Absent>,
        stage: Stage,
    ) -> Self
    {
        Self {
            at,
            expected,
            stage,
        }
    }

    /// The node judged or formed: the goal starting, or the node of the rule
    /// resuming.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(&self) -> CoreNode
    {
        self.at
    }

    /// The type that node was checked against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn expected(&self) -> Maybe<TypeNode, judged::Absent>
    {
        self.expected
    }

    /// Where the machine stood.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stage(&self) -> Stage
    {
        self.stage
    }
}

/// A refused run's state: the refusal, the obligations pending outermost
/// first, the goal under way and the hypotheses the run had opened.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Failure
{
    /// The refusal.
    refusal: CheckRefusal,
    /// The frames pending, outermost first.
    obligations: Vec<Obligation>,
    /// The goal under way.
    pursuit: Pursuit,
    /// The binders the run had opened, outermost first.
    hypotheses: Vec<ValueTypeId>,
}

impl Failure
{
    /// The failure of a run that refused with `refusal` while pursuing
    /// `pursuit`, `obligations` pending and `hypotheses` open.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        refusal: CheckRefusal,
        obligations: Vec<Obligation>,
        pursuit: Pursuit,
        hypotheses: Vec<ValueTypeId>,
    ) -> Self
    {
        Self {
            refusal,
            obligations,
            pursuit,
            hypotheses,
        }
    }

    /// The failure of a refusal met outside any run's frames: no obligation is
    /// pending and no hypothesis is open.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn bare(
        refusal: CheckRefusal,
        pursuit: Pursuit,
    ) -> Self
    {
        Self {
            refusal,
            obligations: Vec::new(),
            pursuit,
            hypotheses: Vec::new(),
        }
    }

    /// The refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refusal(&self) -> CheckRefusal
    {
        self.refusal
    }

    /// The obligations pending, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[Obligation]
    {
        &self.obligations
    }

    /// The goal the run was pursuing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn pursuit(&self) -> Pursuit
    {
        self.pursuit
    }

    /// The types of the binders the run had opened, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn hypotheses(&self) -> &[ValueTypeId]
    {
        &self.hypotheses
    }

    /// Every type node the failure names: the types its refusal compares,
    /// each obligation's expected type and binders, the pursuit's expected
    /// type and the hypotheses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each type node the refusal compares, then the pursuit's
    ///   expected type, then each obligation's expected type and binders in
    ///   order, then the hypotheses, each when present; a node named twice is
    ///   yielded twice.
    /// - provides: the nodes a face spells while the arena is at hand.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal under a thunk names the compared type
    ///   first; a refusal under a bind names the hypothesis it was under.
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    /// - witness: `judgement::tests::a_refusal_under_a_bind_keeps_its_hypothesis`
    #[spec(ensures: |ret| ret.len() >= self.hypotheses.len())]
    #[inline]
    #[must_use]
    pub fn types(&self) -> Vec<TypeNode>
    {
        let compared = self.refusal.compared();
        let present = |side: Maybe<TypeNode, judged::Absent>| match side {
            | Maybe::Present(node) => Some(node),
            | Maybe::Absent(_) => None,
        };
        let mut types: Vec<TypeNode> = [compared.expected, compared.found]
            .into_iter()
            .filter_map(|side| match side {
                | Maybe::Present(node) => Some(node),
                | Maybe::Absent(_) => None,
            })
            .collect();
        types.extend(present(self.pursuit.expected));
        for obligation in &self.obligations {
            types.extend(present(obligation.expected));
            types.extend(obligation.binders.iter().copied().map(TypeNode::Value));
        }
        types.extend(self.hypotheses.iter().copied().map(TypeNode::Value));
        types
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString;
    use alloc::vec::Vec;

    use super::FoldPremise;
    use super::FrameRole;

    #[test]
    fn every_role_has_its_own_name()
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
            FrameRole::StackNext,
            FrameRole::StackBind,
            FrameRole::ListFold(FoldPremise::Element),
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
            FrameRole::ReturnedEndpoint,
            FrameRole::ElementTransportPath,
            FrameRole::ElementTransportMotive,
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
        ];
        let names: Vec<_> = roles.iter().map(ToString::to_string).collect();
        for (index, name) in names.iter().enumerate() {
            assert!(!name.is_empty(), "every role is named");
            assert!(
                names[.. index].iter().all(|earlier| earlier != name),
                "no two frames share a role name: {name}"
            );
        }
        assert_eq!(
            FrameRole::ListFold(FoldPremise::Cons).to_string(),
            "ListFold",
            "every fold premise names the one frame"
        );
    }
}
