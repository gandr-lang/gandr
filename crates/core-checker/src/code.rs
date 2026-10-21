//! Code constants: the bodies a code may unfold to, and the certificate the
//! normaliser's conversion gives each unfolding.
//!
//! # A code position is the one place a type reduces
//!
//! A type compares structurally, former by former, everywhere but at a decode
//! `El c`: there the code `c` is a term, and a constant with a body — `def Num
//! : Type = Integer` — stands for the type its body quotes. The judgement and
//! the kernel bridge both unfold such a constant through
//! [`CodeDefinitions::certify`], which asks `gandr-core-nbe`'s conversion
//! machine whether the constant converts to its body, with a recording sink:
//! the verdict and its trace travel together as a [`Certificate`], and the
//! bridge has the kernel replay the trace before it offers a declaration that
//! rests on the unfolding.
//!
//! # One unfolding per certificate
//!
//! A certificate names one δ-step, the constant against the body it was
//! defined with, so the machine answers it by unfolding and the kernel's replay
//! re-derives it by the same step. A body that is itself a constant is
//! unfolded by a second certificate, and the types a quote carries are reached
//! by the structural walk that called for the unfolding, so the static normal
//! form is assembled from steps each of which replays. Comparing two quotes
//! whole after unfolding inside them would ask the machine to decide codes it
//! declines to look into.
//!
//! # Path endpoints compare structurally
//!
//! Types embed terms in decode codes and in native path endpoints. Path
//! endpoints are closed first-order quoted codes, and their decoded types
//! compare structurally; elsewhere the type walk compares shared trees with a
//! worklist and accepts equal ids without revisiting them. Accepted code
//! definitions therefore take part in type conversion without a second reducer
//! in the checker.
//!
//! # Why one step per certificate
//!
//! The machine compares quotes whole and declines a pair of codes when anything
//! inside them could still unfold, so a whole comparison of `⌜U El(Num)⌝`
//! against `⌜U Integer⌝` would be refused where the stepwise one succeeds, and
//! a certificate of one δ-step is exactly what the kernel's replay re-derives
//! by its own unfolding rule. A static step is certified the same way — one
//! saturated instance of a static definition against its δβ-reduct, one static
//! lambda's redex against its β-reduct — and the walk compares the rest former
//! by former, a rigid instance by its head and its arguments.
//!
//! The alternatives were keeping the comparison structural and refusing code
//! constants with bodies, which leaves `def Num : Type = Integer` unusable in a
//! type, and a reducer local to the checker beside the machine, a second
//! conversion the kernel oracle exists to rule out. The choice reverses when
//! the machine decides codes under quotes, at which point the walk hands the
//! machine each code pair whole and a comparison carries one certificate.
//!
//! # A function to a universe is a function to a code
//!
//! `El` is unquote. A dynamic function whose arms return quotes — a `case`
//! over a presentation's value returning `⌜Integer⌝` in one arm and `⌜Unit⌝`
//! in another — is a first-order function to a code, and its call where a
//! type is read is the decode of `returned(c)`, the code the call returns. A
//! closed returned code steps to that code by running the call; the step is
//! certified as an endpoint is related, its δ-steps held as recorded
//! unfoldings, because the kernel replays it by reading the returned code as
//! its computation and needs every unfolding named in the trace.
//!
//! A call on a binder runs as far as its scrutinee allows. Its run is read
//! back under rigid binders, a definition's own recursion named as its source
//! wrote it, so a decoder's arm `run x <- el(a); run y <- el(b); return (x =>
//! y)` steps `el(Arrow(a, b))` to `⌜U(El(el(a)) → F El(el(b)))⌝`, whose
//! decodes are the ones a signature writes. A call stuck on its binder,
//! `el(c)`, reads back as a returned code and stays a decode over a neutral
//! code: rigid, compared by its code, two nodes of one call the same syntax.
//!
//! This is the recorded design, a Tarski data universe: the codes are an
//! ordinary datatype and `El` a decoder written over them, both bound at the
//! value level, and a decode is a type over a code that is a term. The
//! alternative was a large elimination, a `case` into `Type` with types for
//! arms and `Element` erased, declined in #353: it would make the kernel's
//! types compute by themselves, and the type language has no such former.
//! Static operators were the other route, and they inspect no value: their
//! arguments are codes. The choice reverses for a universe that stops being a
//! data universe, one whose codes are not values a function can case on.
//!
//! An open step carries no dialogue: it is a [`Derivation::Reading`], and the
//! kernel re-derives it by its own reading of the run. The quote such a run
//! returns holds the calls its arms make on the binders, and the machine's
//! code walk compares those returned endpoints by place, never by what they
//! run to, so no dialogue of it relates the two sides. A closed run can
//! return such a quote too, its call on a binder the quote itself opens: a
//! decoder's arm `pi(a, b) => return (+U ((x : el[<](a)) -> -F
//! el[<](b(x))))` steps `el(pi(nat, k))` to a quote holding `el(k(x))`, and
//! the machine declines the pair for its undecided codes. That step is a
//! reading as well; a closed step the machine decides keeps its dialogue. The
//! alternative was a dialogue over that walk, which needs it to decide
//! returned endpoints under quotes; the choice reverses with the reversal
//! above, when the machine decides codes under quotes.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::BinderLevel;
use gandr_core_nbe::DeclineReason;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainCompId;
use gandr_core_nbe::Endpoints;
use gandr_core_nbe::Environment;
use gandr_core_nbe::EvalFault;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::Recursion;
use gandr_core_nbe::ResharingMemo;
use gandr_core_nbe::TermFace;
use gandr_core_nbe::TraceNode;
use gandr_core_nbe::Unfolding;
use gandr_core_nbe::decide;
use gandr_core_nbe::eval_value_within;
use gandr_core_term::BinderDepth;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::instantiate_value;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;
use quenchant_shape::shape::Maybe;

use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;

quenchant_shape::reason_enum! {
    /// Why a constant has no body a code may unfold to.
    pub mod unfolding {
        /// The reason no body is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No accepted definition at that position supplied a body, and
            /// nothing waits on it: an axiom, a refused declaration, a
            /// position never admitted, or a hole as the definitions table
            /// reads it.
            Rigid,
            /// The position is a hole the module owes: a judgement comparing
            /// its decode with a constructor-headed type waits on it.
            Owed,
            /// The position is a declaration suspended on owed holes: a
            /// judgement reading its type waits with it.
            Waiting,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an evaluation claim returned no value.
    pub mod evaluated {
        /// The reason the claim's body reads back to no returner.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The body's normal form under its binders is not `return v`: it
            /// is stuck on a variable, an opaque constant or an effect.
            Stuck,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a traced conversion gave no trace.
    pub mod converted {
        /// The reason the two sides were not shown convertible.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The machine refuted the pair or declined it: the sides differ,
            /// or a variable, an opaque constant or an effect stood where a
            /// value was owed.
            Apart,
            /// Evaluating a side ran out of fuel, or the machine ran past its
            /// budget, before the pair met or parted: unfolding may not end.
            Undecided,
        }
    }
}

/// How many binders a claim stands under, each read as a rigid variable.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OpenBinders(pub u32);

/// The evaluation budget each side of a certified unfolding runs under.
const CODE_FUEL: u32 = 4_096_u32;

/// How many rounds of evaluation and unfolding readback a claim may take
/// before it is undecided: each round unfolds one layer of the definitions
/// the previous round's normal form calls.
const CLAIM_ROUNDS: u32 = 64_u32;

/// The definitions a code may unfold, in admission order.
#[derive(Clone, Debug, Default)]
pub struct CodeDefinitions
{
    /// Each accepted definition's body, by admission position.
    bodies: BTreeMap<ConstantIndex, ValueId>,
    /// The same bodies as the normaliser's chain, lowered into the arena.
    lowered: LoweredChain,
    /// The definitional environment, which seals nothing.
    environment: DefinitionalEnvironment,
}

/// A code checked at a universe above its own level: the readmission writes
/// the kernel's explicit lift where it stands.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Lift
{
    /// The level of the universe the code synthesised.
    natural: Level,
    /// The level of the universe it was checked at, strictly above.
    target: Level,
}

impl Lift
{
    /// The lift of a code of level `natural` to the universe at `target`.
    ///
    /// # Specification
    /// - requires: `target` is strictly above `natural`.
    /// - ensures: the natural and target levels are retained without changing
    ///   their canonical expressions.
    /// - panics: none.
    /// - executable: none — `Level` exposes neither its representation nor a
    ///   const-readable ordering or equality observer; this constructor must
    ///   preserve its existing const interface.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal, smaller and larger value-code universes are
    ///   distinguished by the bridge, and a genuine increase is independently
    ///   checked after export. The witnesses observe the resulting coercion,
    ///   not arbitrary direct construction outside the ordering premise.
    /// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    #[inline]
    #[must_use]
    pub const fn new(
        natural: Level,
        target: Level,
    ) -> Self
    {
        Self { natural, target }
    }

    /// The level of the universe the code synthesised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn natural(&self) -> &Level
    {
        &self.natural
    }

    /// The level of the universe it was checked at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> &Level
    {
        &self.target
    }

    /// Mint the lifted code `⌜Lift (El code) target⌝` in `arena`: the code a
    /// lift stands for, in the vocabulary the kernel reads it in.
    ///
    /// # Specification
    /// - requires: `code` is a value of `arena` whose type is the universe of
    ///   the value sort at [`Self::natural`].
    /// - ensures: a quote of the lift of the type `code` denotes; a quote
    ///   decodes as it is minted, so a quoted `code` lifts its own type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted and named small codes are checked in a larger
    ///   value universe, and kernel readmission observes the explicit lift;
    ///   missing the quote, inner type or target changes that judgement.
    /// - witness: `bridge::tests::a_smaller_type_at_a_larger_universe_readmits_with_a_lift`
    /// - witness: `bridge::tests::a_code_constant_argument_unfolds_at_export`
    #[spec(
        requires: arena.value(code).is_some(),
        ensures: |ret| matches!(arena.value(ret), Some(Value::Quote(quoted))
            if matches!(arena.value_type(*quoted), Some(ValueType::Lift { inner, target })
                if target == self.target() && match arena.value(code) {
                    | Some(&Value::Quote(denoted)) => *inner == denoted,
                    | Some(_) => matches!(arena.value_type(*inner), Some(ValueType::Element { code: held, target: natural })
                        if *held == code && natural == self.natural()),
                    | None => false,
                })),
    )]
    #[inline]
    pub fn mint(
        &self,
        arena: &mut CoreArena,
        code: ValueId,
    ) -> ValueId
    {
        let denoted = arena.value_type_element(code, self.natural.clone());
        let lifted = arena.value_type_lift(denoted, self.target.clone());
        arena.value_quote(lifted)
    }
}

/// What one certified step unfolds: the name a certificate is filed under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unfolded
{
    /// The definition at this module position: a code constant's δ-step, or
    /// a static definition's δβ-step at one saturated instance.
    Definition(ConstantIndex),
    /// The static lambda at this node, met at the head of a static
    /// application: its β-step.
    Abstraction(ValueId),
    /// The returned code at this node, `returned(c)`: the call `c` run to the
    /// quote it returns, the unquote of a function to a universe.
    Returned(ValueId),
}

/// One step of reduction at a code's head: what it unfolds, the code it fires
/// at and the reduct, minted.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Reduction
{
    /// What the step unfolds.
    unfolded: Unfolded,
    /// The code the step fires at.
    redex: ValueId,
    /// The reduct.
    reduct: ValueId,
}

impl Reduction
{
    /// What the step unfolds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unfolded(&self) -> Unfolded
    {
        self.unfolded
    }

    /// The code the step fires at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn redex(&self) -> ValueId
    {
        self.redex
    }

    /// The reduct.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reduct(&self) -> ValueId
    {
        self.reduct
    }
}

/// How the kernel re-derives a certified step.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Derivation
{
    /// By replaying the machine's dialogue, in order.
    Dialogue,
    /// By its own reading of the run, with no dialogue: the step of a returned
    /// code over a binder, whose quote holds calls the machine's code walk
    /// compares only by place.
    Reading,
}

/// The normaliser's certificate that a code converts to the reduct of one
/// step at its head.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Certificate
{
    /// What the step unfolds.
    unfolded: Unfolded,
    /// The code the step fires at.
    redex: ValueId,
    /// The reduct it fires to.
    reduct: ValueId,
    /// The verdict the step was certified at: the machine's for a dialogue,
    /// the run's own for a reading.
    verdict: MachineVerdict,
    /// How the kernel re-derives the step.
    derivation: Derivation,
    /// The derivation the machine recorded, in order; empty for a reading.
    decisions: Vec<ConversionDecision<TraceNode>>,
}

impl Certificate
{
    /// What the step unfolds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unfolded(&self) -> Unfolded
    {
        self.unfolded
    }

    /// The code the step fires at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn redex(&self) -> ValueId
    {
        self.redex
    }

    /// The reduct it fires to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reduct(&self) -> ValueId
    {
        self.reduct
    }

    /// The verdict the step was certified at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> MachineVerdict
    {
        self.verdict
    }

    /// How the kernel re-derives the step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn derivation(&self) -> Derivation
    {
        self.derivation
    }

    /// The derivation the machine recorded, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.decisions
    }

    /// The certificate with its derivation replaced: the seam a test corrupts
    /// a trace through, to witness that the replay refuses it.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    pub(crate) fn with_decisions(
        self,
        decisions: Vec<ConversionDecision<TraceNode>>,
    ) -> Self
    {
        Self { decisions, ..self }
    }

    /// The certificate with its reduct replaced: the seam a test forges a
    /// step's result through, to witness that the replay refuses it.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    pub(crate) fn with_reduct(
        self,
        reduct: ValueId,
    ) -> Self
    {
        Self { reduct, ..self }
    }
}

/// The normaliser's reading of one closed evaluation claim.
///
/// For the claim `thunk (λⁿ. M)`: the normal form it reads back to,
/// `thunk (λⁿ. return v)`, the value `v` its body returns under its `n`
/// binders, and the trace that the claim converts to that normal form.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Evaluation
{
    /// The claim's normal form.
    normal: ValueId,
    /// The value the body returns, under the claim's binders.
    returned: ValueId,
    /// The derivation the machine recorded that the claim converts to its
    /// normal form, in order.
    decisions: Vec<ConversionDecision<TraceNode>>,
}

impl Evaluation
{
    /// The claim's normal form, `thunk (λⁿ. return v)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn normal(&self) -> ValueId
    {
        self.normal
    }

    /// The value the body returns, under the claim's binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn returned(&self) -> ValueId
    {
        self.returned
    }

    /// The derivation that the claim converts to its normal form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.decisions
    }
}

/// The normaliser's reading of one reflexivity: the derivation relating its
/// point to each endpoint of the path type it was checked against.
///
/// Each dialogue is the machine's convertible trace from the point to that
/// endpoint, recorded with returned endpoints held at the definitions they
/// call ([`gandr_core_nbe::Endpoints::Hold`]), so every δ-step an endpoint
/// needs, under a binder or not, is one of its decisions. An endpoint that is
/// the point's own node or syntax relates by the empty dialogue.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Reflexivity
{
    /// The derivation from the point to the left endpoint, in order.
    left: Vec<ConversionDecision<TraceNode>>,
    /// The derivation from the point to the right endpoint, in order.
    right: Vec<ConversionDecision<TraceNode>>,
}

impl Reflexivity
{
    /// The reading relating the point to `left` and to `right` by these
    /// derivations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(
        left: Vec<ConversionDecision<TraceNode>>,
        right: Vec<ConversionDecision<TraceNode>>,
    ) -> Self
    {
        Self { left, right }
    }

    /// The derivation from the point to the left endpoint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn left(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.left
    }

    /// The derivation from the point to the right endpoint.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reflexivity at a point that computes to its right
    ///   endpoint records that derivation, and the bridge crosses it with the
    ///   reflexivity.
    /// - witness: `bridge::tests::a_reflexivity_carries_its_right_endpoint_s_dialogue`
    #[inline]
    #[must_use]
    pub fn right(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.right
    }
}

/// The normaliser's reading of one pair of path endpoints a type conversion
/// met: the derivation relating the left endpoint to the right.
///
/// The dialogue is the machine's convertible trace between the two, recorded
/// as a reflexivity's is, with returned endpoints held at the definitions they
/// call, so every δ-step the pair needs is one of its decisions. The kernel
/// replays it where its own forced reading leaves the two types apart.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EndpointRelation
{
    /// The endpoint the derivation starts from.
    left: ValueId,
    /// The endpoint the derivation ends at.
    right: ValueId,
    /// The derivation from `left` to `right`, in order.
    decisions: Vec<ConversionDecision<TraceNode>>,
}

impl EndpointRelation
{
    /// The reading relating `left` to `right` by `decisions`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(
        left: ValueId,
        right: ValueId,
        decisions: Vec<ConversionDecision<TraceNode>>,
    ) -> Self
    {
        Self {
            left,
            right,
            decisions,
        }
    }

    /// The endpoint the derivation starts from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> ValueId
    {
        self.left
    }

    /// The endpoint the derivation ends at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> ValueId
    {
        self.right
    }

    /// The derivation from the left endpoint to the right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.decisions
    }
}

impl CodeDefinitions
{
    /// No definition: every constant is rigid.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Record `body` as the definition at `constant`.
    ///
    /// # Specification
    /// - requires: `body` is a closed value of the arena every later
    ///   certificate is asked over.
    /// - ensures: [`Self::body`] answers `body` for `constant` when `constant`
    ///   follows every position recorded before it and the chain has entry
    ///   space; otherwise the table is unchanged. An unrecorded position stays
    ///   rigid, and a repeated position keeps its earlier body.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ascending definitions, a skipped lower position and a
    ///   repeated position expose their reducts; these distinguish replacing an
    ///   accepted body, admitting out of order and losing a new definition.
    ///   Exhausting the thirty-two-bit entry space is not constructed.
    /// - witness: `code::tests::definitions_reject_reordering_without_replacing_earlier_bodies`
    /// - witness: `code::tests::a_static_step_reduces_saturated_instances_and_redexes_only`
    #[spec(
        captures: [before = self.body(constant), count = self.bodies.len(), highest = self.bodies.last_key_value().map(|(&position, _)| position)],
        ensures: if u32::try_from(count).is_ok() && highest.is_none_or(|previous| previous < constant) {
            self.body(constant) == Maybe::Present(body) && self.bodies.len().checked_sub(count) == Some(1)
        } else {
            self.body(constant) == before && self.bodies.len() == count
        },
    )]
    #[inline]
    pub fn define(
        &mut self,
        constant: ConstantIndex,
        body: ValueId,
    )
    {
        let Ok(entry) = u32::try_from(self.bodies.len())
        else {
            return;
        };
        if self
            .lowered
            .define(
                constant,
                GlobalIndex::from(entry),
                Transparency::Manifest,
                &[],
                body,
            )
            .is_ok()
        {
            self.bodies.insert(constant, body);
        }
    }

    /// Record the data declaration at `constant` as presented by its
    /// signature's rules, when it has any: every later conversion reads its
    /// terms by their normal forms.
    ///
    /// # Specification
    /// - requires: `signature` formed at `constant`, its rules validated.
    /// - ensures: the lowered chain records the signature's constructor count
    ///   at `constant`, and presents `constant` by the signature's rules over
    ///   its constructor table's arities exactly when the signature has rules;
    ///   a free signature leaves the presentations unchanged.
    /// - provides: the one place a presented type reaches the checker's
    ///   conversion.
    /// - panics: none.
    /// - executable: none — the lowered chain is read only through a
    ///   conversion's definitions; the witness observes the rules there.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle word checks at its reduced word's path type
    ///   once the circle is presented, and is refused over a free circle.
    /// - witness: `tests::native_formers::a_presented_word_meets_its_reduced_word_in_both_checkers`
    #[inline]
    pub fn present(
        &mut self,
        constant: ConstantIndex,
        signature: &gandr_core_term::DataSignature,
    )
    {
        self.lowered.admit_data(
            constant,
            gandr_kernel_term::ConstructorCount::from(signature.constructors().len()),
        );
        let presentation = signature.presentation();
        if presentation.rules().is_empty() {
            return;
        }
        let arities = signature
            .constructors()
            .iter()
            .map(|fields| gandr_kernel_term::FieldCount::from(fields.len()))
            .collect();
        self.lowered.present(
            constant,
            gandr_core_nbe::Presented::new(presentation.clone(), arities),
        );
    }

    /// The body recorded at `constant`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn body(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<ValueId, unfolding::Absent>
    {
        match self.bodies.get(&constant) {
            Some(&body) => Maybe::Present(body),
            None => Maybe::Absent(unfolding::Absent::Rigid),
        }
    }

    /// Every recorded definition, ascending by position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn definitions(&self) -> impl Iterator<Item = (ConstantIndex, ValueId)>
    {
        self.bodies
            .iter()
            .map(|(&constant, &body)| (constant, body))
    }

    /// One step of reduction at `code`'s head: a constant's δ-step, a static
    /// definition's δβ-step at a saturated instance, a static lambda's
    /// β-step at a saturated application, or a closed returned code's run to
    /// the code it returns, its reduct minted into `core`.
    ///
    /// # Specification
    /// - requires: every body this table holds lives in `core`.
    /// - ensures: for a constant with a body, that body, unfolding the
    ///   definition. For a static application, read as its head under its
    ///   arguments in order: at a head that opens `n` static lambdas — a static
    ///   lambda chain, unfolding the abstraction at its outermost, or a
    ///   constant whose body is one, unfolding the definition — and at least
    ///   `n` arguments, the innermost body instantiated at the first `n`
    ///   arguments outermost first, under the rest; with `n` zero, a constant's
    ///   body itself under every argument. For a closed returned code standing
    ///   alone, `returned(c)` where `c` runs to `return v`, the value `v` read
    ///   back with every definition unfolded. [`unfolding::Absent::Rigid`] for
    ///   every other code, an operator short of its arguments, an open returned
    ///   code and a run that does not return included. A step fires at `code`
    ///   itself, and names a definition that has a body, a node that is a
    ///   static lambda, or a node that is a returned code.
    /// - provides: the one step every walk reduces a code by, whose reduct a
    ///   certificate then relates to the code. The kernel's replay re-derives a
    ///   δβ-step by the same saturated substitution, so a lambda chain is
    ///   consumed whole or not at all, as an operator of as many parameters; it
    ///   re-derives a run by reading the returned code as its computation.
    /// - fails: [`CheckRefusal::DanglingNode`] for a node `core` does not hold;
    ///   [`CheckRefusal::Undecided`] at the code when its run faults or runs
    ///   out of fuel.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
    /// - [`CheckRefusal::Undecided`] — a returned code's run faulted.
    ///
    /// # Termination
    /// - reason: `while let` loops descending a head path and a lambda chain,
    ///   and `for` loops over finite argument slices, not recursion.
    /// - measure: the focus's arena position while descending; then the
    ///   arguments left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the arms, separated by a constant unfolding, a
    ///   saturated and an unsaturated instance of a two-parameter operator, a
    ///   saturated and an unsaturated static redex, an instance carrying a
    ///   further argument, a rigid head, and a closed and an open returned
    ///   code.
    /// - witness: `code::tests::a_static_step_reduces_saturated_instances_and_redexes_only`
    /// - witness: `code::tests::a_closed_returned_code_runs_to_the_quote_it_returns`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(step)) => step.redex() == code && match step.unfolded() {
            | Unfolded::Definition(constant) => matches!(self.body(constant), Maybe::Present(_)),
            | Unfolded::Abstraction(head) => matches!(core.value(head), Some(Value::StaticLambda(_))),
            | Unfolded::Returned(at) => at == code && matches!(core.value(at), Some(Value::Returned(_))),
        },
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    pub fn reduce(
        &self,
        core: &mut CoreArena,
        code: ValueId,
    ) -> Result<Maybe<Reduction, unfolding::Absent>, CheckRefusal>
    {
        let rigid = Ok(Maybe::Absent(unfolding::Absent::Rigid));
        let read = |core: &CoreArena, at: ValueId| {
            core.value(at).cloned().ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(at)),
            })
        };
        let mut arguments = Vec::new();
        let mut head = code;
        while let Value::StaticApplication(applied, argument) = read(core, head)? {
            arguments.push(argument);
            head = applied;
        }
        arguments.reverse();
        let (unfolded, mut reduct) = match read(core, head)? {
            Value::StaticLambda(_) => (Unfolded::Abstraction(head), head),
            Value::Returned(_) if arguments.is_empty() => {
                return self.run_returned(core, code);
            },
            Value::Constant(constant) => {
                let Maybe::Present(body) = self.body(constant)
                else {
                    return rigid;
                };
                (Unfolded::Definition(constant), body)
            },
            Value::PathRefl(_)
            | Value::Here(_)
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::SessionRelated { .. }
            | Value::Recorded(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Reify(_)
            | Value::Primitive { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Variable { .. }
            | Value::Tuple(_)
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Literal(_)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..)
            | Value::Hole(_)
            | Value::Mark { .. } => return rigid,
        };
        let mut consumed = 0_usize;
        while let Value::StaticLambda(inner) = read(core, reduct)? {
            let Some(&argument) = arguments.get(consumed)
            else {
                return rigid;
            };
            reduct = instantiate_value(core, inner, argument);
            consumed = consumed
                .checked_add(1)
                .ok_or(CheckRefusal::MachineInvariant)?;
        }
        for &argument in arguments.get(consumed ..).unwrap_or_default() {
            reduct = core.value_static_application(reduct, argument);
        }
        Ok(Maybe::Present(Reduction {
            unfolded,
            redex: code,
            reduct,
        }))
    }

    /// The run of the returned code `code`, standing alone at a code position,
    /// to the code its computation returns.
    ///
    /// # Specification
    /// - requires: every body this table holds lives in `core`.
    /// - ensures: for a `returned(c)` whose computation reads back — every
    ///   definition unfolded, a definition's own recursion named as the
    ///   definition, the binders `c` reaches read as rigid variables — to
    ///   `return v` with `v` no returned code, the step unfolding the returned
    ///   code at `code` to `v`. [`unfolding::Absent::Rigid`] for any other
    ///   node, for a run that waits on a binder before it returns a code — it
    ///   reads back as a returned code — and for a run that reads back stuck.
    /// - provides: the reduct of `El` as unquote: a function to a universe
    ///   returns a quote, and the type at the code position is the quoted one,
    ///   open or closed.
    /// - fails: [`CheckRefusal::Undecided`] at `code` when evaluation or
    ///   readback faults or runs out of fuel; [`CheckRefusal::DanglingNode`]
    ///   for a node `core` does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed call of a function selecting a quote by
    ///   `case` runs to that quote, and the same call on a variable is rigid; a
    ///   decoder's arm on a binder steps to the quote over the decodes its
    ///   source wrote, and an open decode forged to another quote is refused.
    /// - witness: `code::tests::a_closed_returned_code_runs_to_the_quote_it_returns`
    /// - witness: `bridge::tests::an_open_decode_crosses_read_and_a_forged_one_is_refused`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(step)) => step.unfolded() == Unfolded::Returned(code)
            && step.redex() == code
            && core.value(step.reduct()).is_some(),
        | Ok(Maybe::Absent(_)) => true,
        | Err(refusal) => refusal == CheckRefusal::Undecided { at: code }
            || matches!(refusal, CheckRefusal::DanglingNode { .. }),
    })]
    fn run_returned(
        &self,
        core: &mut CoreArena,
        code: ValueId,
    ) -> Result<Maybe<Reduction, unfolding::Absent>, CheckRefusal>
    {
        let Some(&Value::Returned(_)) = core.value(code)
        else {
            return Ok(Maybe::Absent(unfolding::Absent::Rigid));
        };
        let reach = loose_reach(core, CoreNode::Term(TermNode::Value(code)))?;
        let mut body = core.computation_return(code);
        for _binder in 0 .. usize::from(reach) {
            body = core.computation_lambda(body);
        }
        let claim = core.value_thunk(body);
        match self.read_back(core, claim, Recursion::Refolded) {
            Ok(Readback::Returned { returned, .. })
                if !matches!(core.value(returned), Some(&Value::Returned(_))) =>
            {
                Ok(Maybe::Present(Reduction {
                    unfolded: Unfolded::Returned(code),
                    redex: code,
                    reduct: returned,
                }))
            },
            Ok(Readback::Returned { .. } | Readback::Stuck(_) | Readback::Unsuspended) => {
                Ok(Maybe::Absent(unfolding::Absent::Rigid))
            },
            Err(_undecided) => Err(CheckRefusal::Undecided { at: code }),
        }
    }

    /// Certify that the step `step` took holds: its redex converts to its
    /// reduct.
    ///
    /// # Specification
    /// - requires: `step` is a reduction [`Self::reduce`] gave over `core`;
    ///   every body this table holds lives in `core`.
    /// - ensures: the certificate of the machine's verdict on the redex against
    ///   the reduct, each evaluated with the free binders the redex reaches
    ///   read as rigid variables — the reduct reaches no further — the
    ///   derivation a recording sink kept. A closed returned code's run is
    ///   related as an endpoint is, its δ-steps held as recorded unfoldings, so
    ///   the kernel's replay of the code as its computation meets every
    ///   unfolding it needs in the trace. An open returned code's run is
    ///   certified as [`Derivation::Reading`], with no dialogue: its quote
    ///   holds the calls its arms make on the binders, which the machine
    ///   compares by place, and the kernel re-derives the step by its own
    ///   reading. So is a closed run whose dialogue the machine declines for
    ///   its undecided codes: its quote holds a call on a binder the quote
    ///   itself opens, as `pi(a, b)` decodes to `(x : el(a)) -> -F el(b(x))`.
    /// - provides: the one route by which a code position reduces, and the
    ///   derivation the kernel re-derives.
    /// - fails: [`CheckRefusal::Undecided`] at `redex` when either side does
    ///   not evaluate, the machine faults, or its verdict is anything but
    ///   convertible or, for a closed returned code, a decline for undecided
    ///   codes.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — the step was not certified.
    ///
    /// # Termination
    /// - reason: the `for` loop binds one rigid variable per binder the redex
    ///   reaches, not recursion; the machine runs under its own fuel.
    /// - measure: the binders left to bind.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the kernel's replay is the external oracle: every
    ///   certificate a readmission records over generated code constants and
    ///   generated static declarations replays to convertible; the L3 residue
    ///   is a body chained through a second constant, an open instance, and a
    ///   corrupted trace refused.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    /// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
    /// - witness: `bridge::tests::an_unquoted_function_call_crosses_with_its_run_certified`
    /// - witness: `bridge::tests::an_open_decode_crosses_read_and_a_forged_one_is_refused`
    /// - witness: `bridge::tests::a_closed_decode_holding_a_call_under_its_quote_crosses_read`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Ok(ref certificate) => {
            certificate.unfolded() == step.unfolded()
                && certificate.redex() == step.redex()
                && certificate.reduct() == step.reduct()
                && certificate.verdict() == MachineVerdict::Convertible
                && (certificate.derivation() == Derivation::Dialogue || certificate.decisions().is_empty())
        },
        | Err(refusal) => refusal == CheckRefusal::Undecided { at: step.redex() }
            || matches!(refusal, CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant),
    })]
    pub fn certify(
        &self,
        core: &CoreArena,
        step: Reduction,
    ) -> Result<Certificate, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: step.redex };
        if let Unfolded::Returned(_) = step.unfolded {
            let reading = Certificate {
                unfolded: step.unfolded,
                redex: step.redex,
                reduct: step.reduct,
                verdict: MachineVerdict::Convertible,
                derivation: Derivation::Reading,
                decisions: Vec::new(),
            };
            if usize::from(loose_reach(
                core,
                CoreNode::Term(TermNode::Value(step.redex)),
            )?) != 0
            {
                return Ok(reading);
            }
            let (verdict, decisions) = self.relation(core, step.redex, step.reduct)?;
            return match verdict {
                MachineVerdict::Convertible => Ok(Certificate {
                    derivation: Derivation::Dialogue,
                    decisions,
                    ..reading
                }),
                MachineVerdict::Declined(DeclineReason::UndecidedCodes) => Ok(reading),
                MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => Err(undecided),
            };
        }
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
        let mut domain = DomainArena::new();
        let mut environment = Environment::new();
        let reach = loose_reach(core, CoreNode::Term(TermNode::Value(step.redex)))?;
        let open = u32::try_from(usize::from(reach))
            .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        for level in 0 .. open {
            let neutral = domain
                .neutral_node(
                    NeutralHead::Variable {
                        zone: Zone::Intuitionistic,
                        level: BinderLevel::from(level),
                    },
                    Vec::new(),
                    Unfolding::Rigid,
                )
                .map_err(|_fault| undecided)?;
            let bound = domain
                .value_neutral(neutral, TermFace::Reduced)
                .map_err(|_fault| undecided)?;
            environment.extend(Zone::Intuitionistic, bound);
        }
        let fuel = Fuel::from(CODE_FUEL);
        let evaluate = |domain: &mut DomainArena, term: ValueId| {
            eval_value_within(core, domain, definitions, fuel, term, environment.clone())
                .map(|(value, _remaining)| value)
                .map_err(|_fault| undecided)
        };
        let left = evaluate(&mut domain, step.redex)?;
        let right = evaluate(&mut domain, step.reduct)?;
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right).under(BinderLevel::from(open)),
            &mut log,
        )
        .map_err(|_fault| undecided)?;
        match report.verdict() {
            MachineVerdict::Convertible => Ok(Certificate {
                unfolded: step.unfolded,
                redex: step.redex,
                reduct: step.reduct,
                verdict: report.verdict(),
                derivation: Derivation::Dialogue,
                decisions: log.decisions().copied().collect(),
            }),
            MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => Err(undecided),
        }
    }

    /// Decide whether two values standing under the same binders are the same
    /// term: each evaluated with the free binders either reaches read as rigid
    /// variables, every definition this table holds unfolding.
    ///
    /// # Specification
    /// - requires: every body this table holds, and both values, live in
    ///   `core`; the two values stand under the same binders.
    /// - ensures: the machine's verdict on the pair, each side evaluated in one
    ///   environment of rigid variables, one per binder the farther side
    ///   reaches.
    /// - provides: the conversion two terms meet where no derivation is kept:
    ///   function extensionality's pointwise results and a type comparison's
    ///   term pairs.
    /// - fails: [`CheckRefusal::Undecided`] at `left` when either side does not
    ///   evaluate or the machine faults; [`CheckRefusal::DanglingNode`] for a
    ///   node `core` does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`], [`CheckRefusal::DanglingNode`] — as
    ///   above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function extensionality whose pointwise results
    ///   differ is refused, and one whose results agree is decided.
    /// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at } ) if at == left)
        || matches!(ret, Err(CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant)))]
    #[inline]
    pub fn convert_terms(
        &self,
        core: &CoreArena,
        left: ValueId,
        right: ValueId,
    ) -> Result<MachineVerdict, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: left };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
        let mut domain = DomainArena::new();
        let problem = rigid_problem(core, &mut domain, definitions, left, right)?;
        decide::<NullSink, ResharingMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            problem,
            &mut NullSink,
        )
        .map(|report| report.verdict())
        .map_err(|_fault| undecided)
    }

    /// Relate a reflexivity's point to one endpoint standing under the same
    /// binders, recording the derivation: each evaluated with the free
    /// binders either reaches read as rigid variables, every definition this
    /// table holds unfolding, and a returned endpoint held at the definition
    /// it calls.
    ///
    /// # Specification
    /// - requires: every body this table holds, and both values, live in
    ///   `core`; the two values stand under the same binders.
    /// - ensures: the machine's convertible trace from `point` to `endpoint`,
    ///   each side evaluated in one environment of rigid variables, one per
    ///   binder the farther side reaches, under
    ///   [`gandr_core_nbe::Endpoints::Hold`]; [`converted::Absent::Apart`] when
    ///   the machine refutes or declines the pair.
    /// - provides: the endpoint condition of reflexivity's rule and the
    ///   dialogue the kernel replays for it. Holding returned endpoints puts
    ///   every δ-step an endpoint needs in the trace as an `Unfold`, where
    ///   evaluation would otherwise take it silently.
    /// - fails: [`CheckRefusal::Undecided`] at `point` when either side does
    ///   not evaluate or the machine faults; [`CheckRefusal::DanglingNode`] for
    ///   a node `core` does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`], [`CheckRefusal::DanglingNode`] — as
    ///   above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition applied to a variable converts with the
    ///   body it unfolds to, two distinct literals are apart, and an arithmetic
    ///   redex over a variable is apart from the variable; skipping the
    ///   unfolding or the rigid environment changes a verdict. The recorded
    ///   dialogue replays in the kernel against the admitted definitions.
    /// - witness: `judgement::tests::reflexivity_checks_by_endpoint_conversion`
    /// - witness: `bridge::tests::a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at } ) if at == point)
        || matches!(ret, Err(CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant)))]
    #[inline]
    pub fn relate_terms(
        &self,
        core: &CoreArena,
        point: ValueId,
        endpoint: ValueId,
    ) -> Result<Maybe<Vec<ConversionDecision<TraceNode>>, converted::Absent>, CheckRefusal>
    {
        let (verdict, decisions) = self.relation(core, point, endpoint)?;
        Ok(match verdict {
            MachineVerdict::Convertible => Maybe::Present(decisions),
            MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => {
                Maybe::Absent(converted::Absent::Apart)
            },
        })
    }

    /// The machine's verdict on `point` against `endpoint`, each evaluated as
    /// [`Self::relate_terms`] evaluates them, and the dialogue it recorded.
    ///
    /// # Specification
    /// - requires: as [`Self::relate_terms`].
    /// - ensures: the verdict the machine reached, with the decisions its
    ///   recording sink kept; a decline keeps its reason.
    /// - provides: [`Self::relate_terms`]'s answer, and the reason a returned
    ///   step's dialogue was declined, which [`Self::certify`] reads.
    /// - fails: as [`Self::relate_terms`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`], [`CheckRefusal::DanglingNode`] — as
    ///   [`Self::relate_terms`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::relate_terms`], and a decode whose run
    ///   returns a quote holding a call on the quote's own binder declined for
    ///   its undecided codes.
    /// - witness: `judgement::tests::reflexivity_checks_by_endpoint_conversion`
    /// - witness: `bridge::tests::a_closed_decode_holding_a_call_under_its_quote_crosses_read`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at } ) if at == point)
        || matches!(ret, Err(CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant)))]
    fn relation(
        &self,
        core: &CoreArena,
        point: ValueId,
        endpoint: ValueId,
    ) -> Result<(MachineVerdict, Vec<ConversionDecision<TraceNode>>), CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: point };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root())
                .reading_endpoints(Endpoints::Hold);
        let mut domain = DomainArena::new();
        let problem = rigid_problem(core, &mut domain, definitions, point, endpoint)?;
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            problem,
            &mut log,
        )
        .map_err(|_fault| undecided)?;

        Ok((report.verdict(), log.decisions().copied().collect()))
    }

    /// Decide that two computations standing under `open` binders convert,
    /// each evaluated with those binders read as rigid variables and every
    /// definition this table holds unfolding, and keep the machine's trace.
    ///
    /// # Specification
    /// - requires: every body this table holds, and both computations, live in
    ///   `core`; neither reaches past `open` binders.
    /// - ensures: the machine's convertible trace from `left` to `right`, its
    ///   anchors forgotten as the wire forgets them;
    ///   [`converted::Absent::Apart`] when the machine refutes or declines the
    ///   pair.
    /// - provides: the dialogue a universe equivalence's round trip carries,
    ///   which the kernel replays against the claim it regenerates.
    /// - fails: [`CheckRefusal::Undecided`] at `at` when either side does not
    ///   evaluate or the machine faults.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — negation after negation returns its input at both
    ///   injections and the trace replays in the kernel; the identity after
    ///   negation is apart.
    /// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
    /// - witness: `bridge::tests::an_equiv_crosses_as_a_universe_path`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at: found }) if found == at))]
    #[inline]
    pub fn trace_conversion(
        &self,
        core: &CoreArena,
        at: ValueId,
        (left, right): (ComputationId, ComputationId),
        open: OpenBinders,
    ) -> Result<Maybe<Vec<ConversionDecision<()>>, converted::Absent>, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
        let mut domain = DomainArena::new();
        let (one, other) = evaluated_pair(core, &mut domain, definitions, (left, right), open)
            .map_err(|_fault| undecided)?;
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::computations(one, other).under(BinderLevel::from(open.0)),
            &mut log,
        )
        .map_err(|_fault| undecided)?;
        Ok(match report.verdict() {
            MachineVerdict::Convertible => Maybe::Present(
                log.decisions()
                    .copied()
                    .map(|decision| decision.map(|_anchor| ()))
                    .collect(),
            ),
            MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => {
                Maybe::Absent(converted::Absent::Apart)
            },
        })
    }

    /// Decide whether two computations standing under the same binders
    /// convert with no definition unfolding: each evaluated with the binders
    /// either reaches read as rigid variables and every constant compared by
    /// name, a presented type's terms read by their normal forms.
    ///
    /// # Specification
    /// - requires: both computations live in `core` and stand under the same
    ///   binders.
    /// - ensures: `Present` exactly when the machine finds the pair convertible
    ///   under [`gandr_core_nbe::Constants::Rigid`];
    ///   [`converted::Absent::Undecided`] when evaluating a side runs out of
    ///   fuel or the machine declines for its budget;
    ///   [`converted::Absent::Apart`] when it refutes or otherwise declines the
    ///   pair, and when either side does not evaluate or the machine faults.
    /// - provides: the δ-free conversion a case's respect for its type's rules
    ///   is decided by, the one the kernel re-derives by its own forced rules,
    ///   where no constant unfolds either. A pair it cannot decide is not shown
    ///   convertible, which refuses rather than admits.
    /// - fails: never — a fault is an apart answer, a spent budget an undecided
    ///   one.
    /// - panics: none.
    /// - executable: none — the verdict is the machine's on terms it evaluates;
    ///   the witnesses observe both answers through the case rule.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixpoint over the circle that recurses through both
    ///   inverse letters meets itself at the cancelled word, and a case reading
    ///   the letter as written does not.
    /// - witness: `tests::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357`
    #[inline]
    pub fn convert_rigidly(
        &self,
        core: &CoreArena,
        pair: (ComputationId, ComputationId),
    ) -> Maybe<(), converted::Absent>
    {
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root()).rigid();
        convert_computations(core, definitions, pair)
    }

    /// Decide whether two computations standing under the same binders
    /// convert, every definition this table holds unfolding as the machine
    /// needs it: each evaluated with the binders either reaches read as rigid
    /// variables.
    ///
    /// # Specification
    /// - requires: both computations live in `core` and stand under the same
    ///   binders.
    /// - ensures: `Present` exactly when the machine finds the pair convertible
    ///   with this table's definitions unfolding;
    ///   [`converted::Absent::Undecided`] when evaluating a side runs out of
    ///   fuel or the machine declines for its budget;
    ///   [`converted::Absent::Apart`] when it refutes or otherwise declines the
    ///   pair, and when either side does not evaluate or the machine faults.
    /// - provides: the conversion a case's loop obligation is decided by: an
    ///   arm answering with a definition applied at the transported point is
    ///   read by what that definition computes there.
    /// - fails: never — a fault is an apart answer, a spent budget an undecided
    ///   one.
    /// - panics: none.
    /// - executable: none — the verdict is the machine's on terms it evaluates;
    ///   the witnesses observe both answers through the case rule.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case whose point branch runs a definition meets its
    ///   obligation once the definition unfolds, at a family conjugation fixes,
    ///   and is still refused at a fixed left endpoint.
    /// - witness: `tests::native_formers::a_loop_obligation_unfolds_the_arm_s_definitions`
    #[inline]
    pub fn convert_unfolding(
        &self,
        core: &CoreArena,
        pair: (ComputationId, ComputationId),
    ) -> Maybe<(), converted::Absent>
    {
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
        convert_computations(core, definitions, pair)
    }

    /// Evaluate the closed claim `claim`, `thunk (λⁿ. M)`, to the value its
    /// body returns, every definition this table holds unfolding, and record
    /// the trace that the claim converts to its normal form.
    ///
    /// # Specification
    /// - requires: every body this table holds, and `claim`, live in `core`;
    ///   `claim` is closed.
    /// - ensures: the claim's normal form, read back with every unfolding
    ///   spent; when it is `thunk (λⁿ. return v)` for some `n`, the evaluation
    ///   of `v` with the machine's convertible trace from the claim to that
    ///   normal form, and [`evaluated::Absent::Stuck`] for any other normal
    ///   form, with no trace recorded.
    /// - provides: the computation a universe equivalence's translator decides,
    ///   and the dialogue the kernel replays for it.
    /// - fails: [`CheckRefusal::Undecided`] at `claim` when evaluation or
    ///   readback faults or runs out of fuel, or the machine does not convert
    ///   the claim to its normal form.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition applied to a constructor returns the
    ///   branch it selects, an application stuck on a variable is stuck, and
    ///   the trace replays in the kernel against the admitted definition.
    /// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(ref evaluation)) => core.value(evaluation.returned()).is_some(),
        | Ok(Maybe::Absent(_)) => true,
        | Err(refusal) => refusal == CheckRefusal::Undecided { at: claim },
    })]
    #[inline]
    pub fn evaluate_claim(
        &self,
        core: &mut CoreArena,
        claim: ValueId,
    ) -> Result<Maybe<Evaluation, evaluated::Absent>, CheckRefusal>
    {
        let Readback::Returned { normal, returned } =
            self.read_back(core, claim, Recursion::Unrolled)?
        else {
            return Ok(Maybe::Absent(evaluated::Absent::Stuck));
        };
        let decisions = self.claim_trace(core, claim, normal)?;
        Ok(Maybe::Present(Evaluation {
            normal,
            returned,
            decisions,
        }))
    }

    /// Read the closed claim `claim`, `thunk (λⁿ. M)`, to its normal form,
    /// returning or stuck, every definition this table holds unfolding, and
    /// record the trace that the claim converts to it.
    ///
    /// # Specification
    /// - requires: as [`Self::evaluate_claim`].
    /// - ensures: [`Reading::Returned`] with the evaluation
    ///   [`Self::evaluate_claim`] gives when the normal form returns; otherwise
    ///   [`Reading::Stuck`] with the normal form the rounds of evaluation and
    ///   readback settle at and the machine's convertible trace from the claim
    ///   to it.
    /// - provides: each step a function extensionality decides under the
    ///   quantifier: a stuck normal form is where the body applies its
    ///   higher-order argument.
    /// - fails: as [`Self::evaluate_claim`], and [`CheckRefusal::Undecided`] at
    ///   `claim` when the claim reads back to no thunk.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `λf. f(true)` at the generic higher-order pattern
    ///   reads to its stuck application with a trace the kernel replays.
    /// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
    /// - witness: `bridge::tests::a_quantified_funext_crosses_as_a_quantified_evaluation`
    #[spec(ensures: |ret| match ret {
        | Ok(Reading::Returned(ref evaluation)) => core.value(evaluation.returned()).is_some(),
        | Ok(Reading::Stuck(ref reduction)) => core.value(reduction.normal()).is_some(),
        | Err(refusal) => refusal == CheckRefusal::Undecided { at: claim },
    })]
    #[inline]
    pub fn read_claim(
        &self,
        core: &mut CoreArena,
        claim: ValueId,
    ) -> Result<Reading, CheckRefusal>
    {
        match self.read_back(core, claim, Recursion::Unrolled)? {
            Readback::Returned { normal, returned } => {
                let decisions = self.claim_trace(core, claim, normal)?;
                Ok(Reading::Returned(Evaluation {
                    normal,
                    returned,
                    decisions,
                }))
            },
            Readback::Stuck(normal) => {
                let decisions = self.claim_trace(core, claim, normal)?;
                Ok(Reading::Stuck(Stalled { normal, decisions }))
            },
            Readback::Unsuspended => Err(CheckRefusal::Undecided { at: claim }),
        }
    }

    /// Read the closed claim `claim` back, round by round, until its body
    /// returns or a round changes nothing, naming a definition's own recursion
    /// in `recursion`.
    ///
    /// # Specification
    /// - requires: as [`Self::evaluate_claim`].
    /// - ensures: [`Readback::Returned`] at the first round whose readback is
    ///   `thunk (λⁿ. return v)`; [`Readback::Stuck`] at a round that reads back
    ///   what it read; [`Readback::Unsuspended`] for a readback that is no
    ///   thunk.
    /// - fails: [`CheckRefusal::Undecided`] at `claim` when evaluation or
    ///   readback faults or runs out of fuel, or the rounds run out.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Termination
    /// - reason: the outer `loop` runs at most [`CLAIM_ROUNDS`] rounds and the
    ///   inner `while let` peels one lambda of the finite normal form per turn,
    ///   not recursion; evaluation and readback run under their own fuel.
    /// - measure: the rounds left, then the lambdas left above the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::evaluate_claim`] and [`Self::read_claim`].
    /// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
    /// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
    #[spec(ensures: |ret| match ret {
        | Ok(Readback::Returned { normal, returned }) => core.value(normal).is_some() && core.value(returned).is_some(),
        | Ok(Readback::Stuck(normal)) => core.value(normal).is_some(),
        | Ok(Readback::Unsuspended) => true,
        | Err(refusal) => refusal == CheckRefusal::Undecided { at: claim },
    })]
    fn read_back(
        &self,
        core: &mut CoreArena,
        claim: ValueId,
        recursion: Recursion,
    ) -> Result<Readback, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: claim };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root())
                .reading_recursion(recursion);
        let fuel = Fuel::from(CODE_FUEL);
        let mut current = claim;
        let mut rounds = 0_u32;
        loop {
            let mut domain = DomainArena::new();
            let evaluated =
                gandr_core_nbe::eval_value(core, &mut domain, definitions, fuel, current)
                    .map_err(|_fault| undecided)?;
            let read = gandr_core_nbe::readback_value(
                core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                fuel,
                evaluated,
            )
            .map_err(|_fault| undecided)?;
            let Some(&Value::Thunk(mut body)) = core.value(read)
            else {
                return Ok(Readback::Unsuspended);
            };
            while let Some(&Computation::Lambda(inner)) = core.computation(body) {
                body = inner;
            }
            if let Some(&Computation::Return(returned)) = core.computation(body) {
                return Ok(Readback::Returned {
                    normal: read,
                    returned,
                });
            }
            if equal_certificate_syntax(core, read, current) == CertificateEquality::Equal {
                return Ok(Readback::Stuck(read));
            }
            rounds = rounds.checked_add(1).ok_or(undecided)?;
            if rounds >= CLAIM_ROUNDS {
                return Err(undecided);
            }
            current = read;
        }
    }

    /// The machine's convertible trace from the closed claim `claim` to its
    /// normal form `normal`, recorded with returned endpoints held at the
    /// definitions they call ([`gandr_core_nbe::Endpoints::Hold`]).
    ///
    /// # Specification
    /// - requires: as [`Self::evaluate_claim`]; `normal` is the claim's
    ///   readback.
    /// - ensures: the decisions the machine recorded converting the two, in
    ///   order; every δ-step the claim takes, a returned endpoint's among them,
    ///   is one of those decisions.
    /// - fails: [`CheckRefusal::Undecided`] at `claim` when either side does
    ///   not evaluate or the machine does not convert them.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::evaluate_claim`] and [`Self::read_claim`];
    ///   a function carried along a named path, `⟨tr(x. x → x, p, f)⟩`, runs
    ///   through `p`'s definition, and a run left to the evaluation records no
    ///   step for it, so the kernel's replay, which unfolds `p` only on a
    ///   recorded step, refuses what the checker accepted.
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    /// - witness: `bridge::tests::a_quantified_funext_crosses_as_a_quantified_evaluation`
    /// - witness: `bridge::tests::a_funext_through_a_named_equivalence_crosses_with_its_unfolding_1335`
    #[spec(ensures: |ret| ret.is_ok() || ret == Err(CheckRefusal::Undecided { at: claim }))]
    fn claim_trace(
        &self,
        core: &CoreArena,
        claim: ValueId,
        normal: ValueId,
    ) -> Result<Vec<ConversionDecision<TraceNode>>, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: claim };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root())
                .reading_endpoints(gandr_core_nbe::Endpoints::Hold);
        let fuel = Fuel::from(CODE_FUEL);
        let mut domain = DomainArena::new();
        let left = gandr_core_nbe::eval_value(core, &mut domain, definitions, fuel, claim)
            .map_err(|_fault| undecided)?;
        let right = gandr_core_nbe::eval_value(core, &mut domain, definitions, fuel, normal)
            .map_err(|_fault| undecided)?;
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right),
            &mut log,
        )
        .map_err(|_fault| undecided)?;
        if report.verdict() != MachineVerdict::Convertible {
            return Err(undecided);
        }
        Ok(log.decisions().copied().collect())
    }
}

/// How a claim read back, round by round.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Readback
{
    /// The body returns: the normal form and the value it returns.
    Returned
    {
        /// The normal form, `thunk (λⁿ. return v)`.
        normal: ValueId,
        /// The value returned, under the claim's binders.
        returned: ValueId,
    },
    /// A round read back what it read: the normal form, which does not return.
    Stuck(ValueId),
    /// The readback is no thunk.
    Unsuspended,
}

/// The normaliser's reading of one closed claim, returning or stuck.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Reading
{
    /// The body returns a value.
    Returned(Evaluation),
    /// The body's normal form does not return.
    Stuck(Stalled),
}

/// The normaliser's reading of one closed claim whose normal form does not
/// return: the normal form, `thunk (λⁿ. M)` with `M` stuck, and the trace that
/// the claim converts to it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Stalled
{
    /// The claim's normal form.
    normal: ValueId,
    /// The derivation the machine recorded that the claim converts to its
    /// normal form, in order.
    decisions: Vec<ConversionDecision<TraceNode>>,
}

impl Stalled
{
    /// The claim's normal form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn normal(&self) -> ValueId
    {
        self.normal
    }

    /// The derivation that the claim converts to its normal form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[ConversionDecision<TraceNode>]
    {
        &self.decisions
    }
}

/// The machine problem relating two values standing under the same binders:
/// each evaluated under `definitions` in one environment of rigid variables,
/// one per binder the farther side reaches.
///
/// # Specification
/// - requires: every body `definitions` holds, and both values, live in `core`;
///   the two values stand under the same binders.
/// - ensures: the problem between both evaluations, under as many binders as
///   the environment binds.
/// - provides: the shared preamble of [`CodeDefinitions::convert_terms`] and
///   [`CodeDefinitions::relate_terms`], which differ only in the reading of a
///   returned endpoint and in the sink.
/// - fails: [`CheckRefusal::Undecided`] at `left` when either side does not
///   evaluate; [`CheckRefusal::DanglingNode`] for a node `core` does not hold;
///   [`CheckRefusal::MachineInvariant`] for a reach past the address space.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the `for` loop binds one rigid variable per binder the sides
///   reach, not recursion; evaluation runs under its own fuel.
/// - measure: the binders left to bind.
///
/// # Adequacy
/// - hypothesis: L3 — a definition applied to a variable converts with the body
///   it unfolds to, which needs the rigid environment.
/// - witness: `judgement::tests::reflexivity_checks_by_endpoint_conversion`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::Undecided { at } ) if at == left)
    || matches!(ret, Err(CheckRefusal::DanglingNode { .. } | CheckRefusal::MachineInvariant)))]
fn rigid_problem(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    left: ValueId,
    right: ValueId,
) -> Result<Problem, CheckRefusal>
{
    let undecided = CheckRefusal::Undecided { at: left };
    let mut environment = Environment::new();
    let reach = |endpoint| loose_reach(core, CoreNode::Term(TermNode::Value(endpoint)));
    let reach = usize::from(reach(left)?).max(usize::from(reach(right)?));
    let open = u32::try_from(reach).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
    for level in 0 .. open {
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(level),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .map_err(|_fault| undecided)?;
        let bound = domain
            .value_neutral(neutral, TermFace::Reduced)
            .map_err(|_fault| undecided)?;
        environment.extend(Zone::Intuitionistic, bound);
    }
    let fuel = Fuel::from(CODE_FUEL);
    let mut evaluate = |term: ValueId| {
        eval_value_within(core, domain, definitions, fuel, term, environment.clone())
            .map(|(value, _remaining)| value)
            .map_err(|_fault| undecided)
    };
    let one = evaluate(left)?;
    let other = evaluate(right)?;
    Ok(Problem::values(one, other).under(BinderLevel::from(open)))
}

/// Decide whether two computations standing under the same binders convert
/// at the stance `definitions` holds: each evaluated with the binders either
/// reaches read as rigid variables.
///
/// # Specification
/// - requires: both computations live in `core` and stand under the same
///   binders.
/// - ensures: `Present` exactly when the machine finds the pair convertible
///   with `definitions`; [`converted::Absent::Undecided`] when evaluating a
///   side runs out of fuel or the machine declines for its budget;
///   [`converted::Absent::Apart`] when it refutes or otherwise declines the
///   pair, and when either side does not evaluate or the machine faults.
/// - provides: the body of [`CodeDefinitions::convert_rigidly`] and
///   [`CodeDefinitions::convert_unfolding`], which differ only in the stance.
/// - fails: never — a fault is an apart answer, a spent budget an undecided
///   one.
/// - panics: none.
/// - executable: none — the verdict is the machine's on terms it evaluates.
///
/// # Adequacy
/// - hypothesis: L3 — as the two callers.
/// - witness: `tests::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357`
/// - witness: `tests::native_formers::a_loop_obligation_unfolds_the_arm_s_definitions`
fn convert_computations(
    core: &CoreArena,
    definitions: Definitions<'_>,
    (left, right): (ComputationId, ComputationId),
) -> Maybe<(), converted::Absent>
{
    let apart = Maybe::Absent(converted::Absent::Apart);
    let reach = |side| loose_reach(core, CoreNode::Term(TermNode::Computation(side)));
    let (Ok(one), Ok(other)) = (reach(left), reach(right))
    else {
        return apart;
    };
    let Ok(open) = u32::try_from(usize::from(one).max(usize::from(other)))
    else {
        return apart;
    };
    let open = OpenBinders(open);
    let mut domain = DomainArena::new();
    let (one, other) = match evaluated_pair(core, &mut domain, definitions, (left, right), open) {
        Ok(pair) => pair,
        Err(EvalFault::OutOfFuel) => return Maybe::Absent(converted::Absent::Undecided),
        Err(_) => return apart,
    };
    let decided = decide::<NullSink, ResharingMemo>(
        core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::computations(one, other).under(BinderLevel::from(open.0)),
        &mut NullSink,
    );
    match decided.map(|report| report.verdict()) {
        Ok(MachineVerdict::Convertible) => Maybe::Present(()),
        Ok(MachineVerdict::Declined(DeclineReason::Budget)) => {
            Maybe::Absent(converted::Absent::Undecided)
        },
        Ok(MachineVerdict::NotConvertible | MachineVerdict::Declined(_)) | Err(_) => apart,
    }
}

/// Evaluate two computations standing under `open` binders, each binder read
/// as a rigid variable, in one environment.
///
/// # Specification
/// - requires: both computations live in `core`; neither reaches past `open`
///   binders.
/// - ensures: both evaluations, in the order given, over one environment of
///   `open` rigid intuitionistic variables, the innermost binder the newest.
/// - provides: the shared preamble of [`CodeDefinitions::trace_conversion`] and
///   [`convert_computations`], which differ in what unfolds and in the sink.
/// - fails: the evaluator's fault, for a side that does not evaluate or a
///   neutral the domain cannot mint.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop binds one rigid variable per open binder, not
///   recursion; evaluation runs under its own fuel.
/// - measure: the binders left to bind.
///
/// # Adequacy
/// - hypothesis: L3 — negation after negation returns its input under the
///   pattern's binders and traces, which needs the rigid environment.
/// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(one, other)| domain.computation(one).is_some() && domain.computation(other).is_some()))]
fn evaluated_pair(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    (left, right): (ComputationId, ComputationId),
    open: OpenBinders,
) -> Result<(DomainCompId, DomainCompId), EvalFault>
{
    let mut environment = Environment::new();
    for level in 0 .. open.0 {
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(level),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .map_err(EvalFault::Domain)?;
        let bound = domain
            .value_neutral(neutral, TermFace::Reduced)
            .map_err(EvalFault::Domain)?;
        environment.extend(Zone::Intuitionistic, bound);
    }
    let fuel = Fuel::from(CODE_FUEL);
    let mut evaluate = |term: ComputationId| {
        gandr_core_nbe::eval_comp_within(core, domain, definitions, fuel, term, environment.clone())
            .map(|(produced, _remaining)| produced)
    };
    let one = evaluate(left)?;
    let other = evaluate(right)?;
    Ok((one, other))
}

/// How many binders outside `root` its free intuitionistic variables reach:
/// one past the largest index that counts out of every binder within `root`,
/// which is a value, a computation or a type of either.
///
/// # Specification
/// - requires: nothing.
/// - ensures: zero for a closed node; otherwise the least `n` such that `root`
///   read beneath `n` binders mentions no binder beyond them. Linear variables
///   count no binder and reach nothing.
/// - provides: the environment a certificate evaluates an open code in, and the
///   closedness an identity's carrier needs.
/// - fails: [`CheckRefusal::DanglingNode`] for a node `core` does not hold;
///   [`CheckRefusal::MachineInvariant`] for a reach past the address space.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the `while let` loop over an explicit worklist, not recursion.
/// - measure: the multiset of arena positions on the worklist: a node is
///   replaced by its children, minted before it within a family; a crossing
///   between families goes to a node the parent holds, and the arena is finite
///   and acyclic across them.
///
/// # Adequacy
/// - hypothesis: L3 — separated by a closed code, a bare variable, a variable
///   beneath a static lambda, a variable beneath a dependent arrow's binder
///   inside a quote, and a type decoding a variable, each reach asserted.
/// - witness: `code::tests::the_loose_reach_counts_only_binders_outside_the_root`
#[inline]
#[spec(ensures: |ret| match (root, ret) {
    | (CoreNode::Term(TermNode::Value(at)), Ok(reach)) => match core.value(at) {
        | Some(&Value::Variable { zone: Zone::Intuitionistic, index }) => {
            usize::try_from(u32::from(index)).ok().and_then(|counted| counted.checked_add(1))
                == Some(usize::from(reach))
        },
        | Some(&(Value::Constant(_) | Value::Literal(_))) => reach == BinderDepth::default(),
        | Some(&Value::Tuple(ref components)) if components.is_empty() => {
            reach == BinderDepth::default()
        },
        | _ => true,
    },
    | _ => true,
})]
pub fn loose_reach(
    core: &CoreArena,
    root: CoreNode,
) -> Result<BinderDepth, CheckRefusal>
{
    let dangling = |node| CheckRefusal::DanglingNode { node };
    let mut reach = 0_usize;
    let mut work = Vec::from([(root, 0_usize)]);
    while let Some((node, depth)) = work.pop() {
        let under = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        match node {
            CoreNode::Term(TermNode::Value(at)) => {
                match *core.value(at).ok_or_else(|| dangling(node))? {
                    Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(datatype)), depth));
                        work.extend(
                            fields
                                .iter()
                                .map(|&field| (CoreNode::Term(TermNode::Value(field)), depth)),
                        );
                    },
                    Value::Record(ref fields) => work.extend(
                        fields
                            .values()
                            .map(|&field| (CoreNode::Term(TermNode::Value(field)), depth)),
                    ),
                    Value::Reify(ref frames) => {
                        for frame in frames.iter() {
                            match *frame {
                                gandr_core_term::control::StackFrame::Apply(value) => {
                                    work.push((CoreNode::Term(TermNode::Value(value)), depth));
                                },
                                gandr_core_term::control::StackFrame::Bind(body) => {
                                    work.push((CoreNode::Term(TermNode::Computation(body)), under));
                                },
                                gandr_core_term::control::StackFrame::Project(_) => {},
                            }
                        }
                    },
                    Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ..
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(path_type)), depth));
                        work.push((CoreNode::Term(TermNode::Value(forward)), depth));
                        work.push((CoreNode::Term(TermNode::Value(backward)), depth));
                    },
                    Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    } => {
                        let outside = usize::try_from(u32::from(index))
                            .ok()
                            .and_then(|counted| counted.checked_add(1))
                            .ok_or(CheckRefusal::MachineInvariant)?;
                        reach = reach.max(outside.saturating_sub(depth));
                    },
                    Value::Primitive { .. }
                    | Value::Variable {
                        zone: Zone::Linear, ..
                    }
                    | Value::Constant(_)
                    | Value::ListNil
                    | Value::Literal(_)
                    | Value::Hole(_) => {},
                    Value::Tuple(ref components) => work.extend(
                        components
                            .iter()
                            .map(|&component| (CoreNode::Term(TermNode::Value(component)), depth)),
                    ),
                    Value::Recorded(ref moves) => {
                        work.extend(
                            moves
                                .iter()
                                .filter_map(|movement| match movement.payload() {
                                    Maybe::Present(payload) => {
                                        Some((CoreNode::Term(TermNode::Value(payload)), depth))
                                    },
                                    Maybe::Absent(_) => None,
                                }),
                        );
                    },
                    Value::PathProduct(first, second)
                    | Value::Funext(first, second)
                    | Value::Equiv(first, second)
                    | Value::Univalence(first, second)
                    | Value::Then(first, second)
                    | Value::FlowProduct(first, second)
                    | Value::FunctionFlow(first, second)
                    | Value::SessionRelated {
                        source: first,
                        target: second,
                        ..
                    }
                    | Value::Ua {
                        forward: first,
                        backward: second,
                        ..
                    }
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second) => {
                        work.push((CoreNode::Term(TermNode::Value(first)), depth));
                        work.push((CoreNode::Term(TermNode::Value(second)), depth));
                    },
                    Value::PathRefl(body)
                    | Value::Here(body)
                    | Value::Stay(body)
                    | Value::Forward(body)
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. }
                    | Value::Mark { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(body)), depth));
                    },
                    Value::StaticLambda(body) => {
                        work.push((CoreNode::Term(TermNode::Value(body)), under));
                    },
                    Value::Thunk(body)
                    | Value::Returned(body)
                    | Value::Nested(body)
                    | Value::Run(body) => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), depth));
                    },
                    Value::Quote(quoted) => {
                        work.push((CoreNode::Type(TypeNode::Value(quoted)), depth));
                    },
                    Value::QuoteComputation(quoted) => {
                        work.push((CoreNode::Type(TypeNode::Computation(quoted)), depth));
                    },
                }
            },
            CoreNode::Term(TermNode::Computation(at)) => {
                match *core.computation(at).ok_or_else(|| dangling(node))? {
                    Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => {
                        work.push((CoreNode::Term(TermNode::Value(scrutinee)), depth));
                        work.push((CoreNode::Type(TypeNode::Computation(motive)), under));
                        work.extend(
                            branches.iter().map(|&branch| {
                                (CoreNode::Term(TermNode::Computation(branch)), depth)
                            }),
                        );
                    },
                    Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _) => {
                        work.push((CoreNode::Term(TermNode::Value(record)), depth));
                    },
                    Computation::Split {
                        scrutinee,
                        arity,
                        motive,
                        body,
                    } => {
                        let inside = depth
                            .checked_add(usize::from(arity))
                            .ok_or(CheckRefusal::MachineInvariant)?;
                        work.push((CoreNode::Term(TermNode::Value(scrutinee)), depth));
                        if let gandr_core_term::SplitMotive::Scrutinee(motive) = motive {
                            work.push((CoreNode::Type(TypeNode::Computation(motive)), under));
                        }
                        work.push((CoreNode::Term(TermNode::Computation(body)), inside));
                    },
                    Computation::Perform {
                        ref signature,
                        payload,
                        ..
                    } => {
                        work.extend(
                            signature
                                .types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.push((CoreNode::Term(TermNode::Value(payload)), depth));
                    },
                    Computation::Exercise {
                        capability,
                        ref signature,
                        payload,
                        ..
                    } => {
                        work.extend(
                            signature
                                .types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.push((CoreNode::Term(TermNode::Value(capability)), depth));
                        work.push((CoreNode::Term(TermNode::Value(payload)), depth));
                    },
                    Computation::Scope {
                        ref signature,
                        subject,
                        on_return,
                        ref clauses,
                    } => {
                        let clause_depth =
                            under.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
                        work.extend(
                            signature
                                .types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.extend(clauses.iter().map(|clause| {
                            (
                                CoreNode::Term(TermNode::Computation(clause.body)),
                                clause_depth,
                            )
                        }));
                        work.extend([
                            (CoreNode::Term(TermNode::Computation(subject)), under),
                            (CoreNode::Term(TermNode::Computation(on_return)), under),
                        ]);
                    },
                    Computation::Handle {
                        ref signature,
                        subject,
                        on_return,
                        ref clauses,
                    } => {
                        let clause_depth =
                            under.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
                        work.extend(
                            signature
                                .types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.extend(clauses.iter().map(|clause| {
                            (
                                CoreNode::Term(TermNode::Computation(clause.body)),
                                clause_depth,
                            )
                        }));
                        work.extend([
                            (CoreNode::Term(TermNode::Computation(subject)), depth),
                            (CoreNode::Term(TermNode::Computation(on_return)), under),
                        ]);
                    },
                    Computation::Resume(stack, body) => work.extend([
                        (CoreNode::Term(TermNode::Value(stack)), depth),
                        (CoreNode::Term(TermNode::Computation(body)), depth),
                    ]),
                    Computation::With(ref components) => {
                        work.extend(components.iter().map(|&component| {
                            (CoreNode::Term(TermNode::Computation(component)), depth)
                        }));
                    },
                    Computation::Ascribe { body, ty } => work.extend([
                        (CoreNode::Term(TermNode::Computation(body)), depth),
                        (CoreNode::Type(TypeNode::Computation(ty)), depth),
                    ]),
                    Computation::Reset(body)
                    | Computation::Project(_, body)
                    | Computation::Mark { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), depth));
                    },
                    Computation::Shift(body)
                    | Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), under));
                    },
                    Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        let cell_depth =
                            under.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
                        work.extend([
                            (CoreNode::Type(TypeNode::Value(element)), depth),
                            (CoreNode::Type(TypeNode::Value(result)), depth),
                            (CoreNode::Term(TermNode::Value(list)), depth),
                            (CoreNode::Term(TermNode::Computation(on_nil)), depth),
                            (CoreNode::Term(TermNode::Computation(on_cons)), cell_depth),
                        ]);
                    },
                    Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        let cell_depth =
                            under.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
                        work.extend([
                            (CoreNode::Term(TermNode::Value(list)), depth),
                            (CoreNode::Term(TermNode::Computation(on_nil)), depth),
                            (CoreNode::Term(TermNode::Computation(on_cons)), cell_depth),
                        ]);
                    },
                    Computation::Primitive { arguments, .. } => {
                        work.extend(
                            arguments.iter().map(|argument| {
                                (CoreNode::Term(TermNode::Value(*argument)), depth)
                            }),
                        );
                    },
                    Computation::Transport(path, value) => {
                        work.push((CoreNode::Term(TermNode::Value(path)), depth));
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    Computation::PathTransport {
                        motive,
                        path,
                        value,
                    }
                    | Computation::Ride {
                        motive,
                        flow: path,
                        value,
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(motive)), under));
                        work.push((CoreNode::Term(TermNode::Value(path)), depth));
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        over,
                        value,
                    } => {
                        work.push((CoreNode::Type(TypeNode::Computation(motive)), depth));
                        for child in [path, start, over, value] {
                            work.push((CoreNode::Term(TermNode::Value(child)), depth));
                        }
                    },
                    Computation::Application(head, argument) => {
                        work.push((CoreNode::Term(TermNode::Computation(head)), depth));
                        work.push((CoreNode::Term(TermNode::Value(argument)), depth));
                    },
                    Computation::Return(value)
                    | Computation::Abandon(value)
                    | Computation::Force(value) => {
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    Computation::Bind(bound, body) => {
                        work.push((CoreNode::Term(TermNode::Computation(bound)), depth));
                        work.push((CoreNode::Term(TermNode::Computation(body)), under));
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        work.push((CoreNode::Term(TermNode::Value(scrutinee)), depth));
                        work.extend(
                            branches.iter().map(|&branch| {
                                (CoreNode::Term(TermNode::Computation(branch)), under)
                            }),
                        );
                    },
                    Computation::Session(ref action) => {
                        // A fork binds linearly, which this intuitionistic
                        // reach does not count.
                        work.extend(
                            action
                                .values()
                                .map(|value| (CoreNode::Term(TermNode::Value(value)), depth)),
                        );
                        work.extend(
                            action
                                .value_types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.extend(
                            action
                                .computations()
                                .map(|child| (CoreNode::Term(TermNode::Computation(child)), depth)),
                        );
                    },
                    Computation::Memory(ref form) => {
                        // A memory form binds linearly, which this
                        // intuitionistic reach does not count.
                        work.extend(
                            form.values()
                                .map(|value| (CoreNode::Term(TermNode::Value(value)), depth)),
                        );
                        work.extend(
                            form.computations()
                                .map(|child| (CoreNode::Term(TermNode::Computation(child)), depth)),
                        );
                    },
                    Computation::World(form) => match form {
                        gandr_core_term::world::WorldForm::Hold { value } => {
                            work.push((CoreNode::Term(TermNode::Value(value)), depth));
                        },
                        gandr_core_term::world::WorldForm::Leta { value, body } => {
                            work.push((CoreNode::Term(TermNode::Value(value)), depth));
                            work.push((CoreNode::Term(TermNode::Computation(body)), under));
                        },
                        gandr_core_term::world::WorldForm::Migrate { body, .. } => {
                            work.push((CoreNode::Term(TermNode::Computation(body)), depth));
                        },
                    },
                    Computation::Hole(_) => {},
                }
            },
            CoreNode::Type(TypeNode::Value(at)) => {
                match *core.value_type(at).ok_or_else(|| dangling(node))? {
                    ValueType::Data { ref arguments, .. } => work.extend(
                        arguments
                            .iter()
                            .map(|&argument| (CoreNode::Term(TermNode::Value(argument)), depth)),
                    ),
                    ValueType::Record(ref fields) => work.extend(
                        fields
                            .values()
                            .map(|&field| (CoreNode::Type(TypeNode::Value(field)), depth)),
                    ),
                    ValueType::Stack { input, output } => work.extend([
                        (CoreNode::Type(TypeNode::Computation(input)), depth),
                        (CoreNode::Type(TypeNode::Computation(output)), depth),
                    ]),
                    ValueType::PathUniverse(source, target) => {
                        work.push((CoreNode::Term(TermNode::Value(source)), depth));
                        work.push((CoreNode::Term(TermNode::Value(target)), depth));
                    },
                    ValueType::Path {
                        carrier,
                        left,
                        right,
                    } => work.extend([
                        (CoreNode::Type(TypeNode::Value(carrier)), depth),
                        (CoreNode::Term(TermNode::Value(left)), depth),
                        (CoreNode::Term(TermNode::Value(right)), depth),
                    ]),
                    ValueType::Flow {
                        carrier,
                        source,
                        target,
                    } => work.extend([
                        (CoreNode::Type(TypeNode::Value(carrier)), depth),
                        (CoreNode::Term(TermNode::Value(source)), depth),
                        (CoreNode::Term(TermNode::Value(target)), depth),
                    ]),
                    ValueType::Run(session) => {
                        work.push((CoreNode::Term(TermNode::Value(session)), depth));
                    },
                    ValueType::Staged { base, .. } | ValueType::Kept { value: base, .. } => {
                        work.push((CoreNode::Type(TypeNode::Value(base)), depth));
                    },
                    ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                        work.extend(
                            parts
                                .iter()
                                .map(|&part| (CoreNode::Type(TypeNode::Value(part)), depth)),
                        );
                    },
                    ValueType::Session(ref session) => {
                        work.extend(
                            session
                                .payloads()
                                .iter()
                                .map(|&payload| (CoreNode::Type(TypeNode::Value(payload)), depth)),
                        );
                    },
                    ValueType::World(ref world) => work.extend(
                        world
                            .types()
                            .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                    ),
                    ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown
                    | ValueType::Buffer => {},
                    ValueType::Capability { ref authority, .. } => work.extend(
                        authority
                            .types()
                            .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                    ),
                    ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(first)), depth));
                        work.push((CoreNode::Type(TypeNode::Value(second)), depth));
                    },
                    ValueType::Sigma { first, second } => {
                        work.push((CoreNode::Type(TypeNode::Value(first)), depth));
                        work.push((CoreNode::Type(TypeNode::Value(second)), under));
                    },
                    ValueType::Thunk(body) => {
                        work.push((CoreNode::Type(TypeNode::Computation(body)), depth));
                    },
                    ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                        work.push((CoreNode::Type(TypeNode::Value(inner)), depth));
                    },
                    ValueType::Element { code, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(code)), depth));
                    },
                }
            },
            CoreNode::Type(TypeNode::Computation(at)) => {
                match *core.comp_type(at).ok_or_else(|| dangling(node))? {
                    CompType::With(ref components) => {
                        work.extend(components.iter().map(|&component| {
                            (CoreNode::Type(TypeNode::Computation(component)), depth)
                        }));
                    },
                    CompType::Returner {
                        result,
                        ref effects,
                    } => {
                        work.extend(
                            effects
                                .types()
                                .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                        );
                        work.push((CoreNode::Type(TypeNode::Value(result)), depth));
                    },
                    CompType::Arrow { domain, codomain } => {
                        work.push((CoreNode::Type(TypeNode::Value(domain)), depth));
                        work.push((CoreNode::Type(TypeNode::Computation(codomain)), depth));
                    },
                    CompType::Pi { domain, codomain } => {
                        work.push((CoreNode::Type(TypeNode::Value(domain)), depth));
                        work.push((CoreNode::Type(TypeNode::Computation(codomain)), under));
                    },
                    CompType::Element { code, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(code)), depth));
                    },
                    CompType::Codata { ref arguments, .. } => work.extend(
                        arguments
                            .iter()
                            .map(|&argument| (CoreNode::Term(TermNode::Value(argument)), depth)),
                    ),
                    CompType::Unknown => {},
                }
            },
        }
    }
    Ok(BinderDepth::from(reach))
}

#[cfg(test)]
mod tests;
