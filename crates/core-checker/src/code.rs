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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::BinderLevel;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Endpoints;
use gandr_core_nbe::Environment;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ReadbackMode;
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
            /// No accepted definition at that position supplied a body: an
            /// axiom, an owed hole, a refused declaration, or a position never
            /// admitted.
            Rigid,
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
    /// The machine's verdict.
    verdict: MachineVerdict,
    /// The derivation the machine recorded, in order.
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

    /// The machine's verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> MachineVerdict
    {
        self.verdict
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
            | Some(&body) => Maybe::Present(body),
            | None => Maybe::Absent(unfolding::Absent::Rigid),
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
    /// definition's δβ-step at a saturated instance, or a static lambda's
    /// β-step at a saturated application, its reduct minted into `core`.
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
    ///   body itself under every argument. [`unfolding::Absent::Rigid`] for
    ///   every other code, an operator short of its arguments included. A step
    ///   fires at `code` itself, and names a definition that has a body or a
    ///   node that is a static lambda.
    /// - provides: the one step every walk reduces a code by, whose reduct a
    ///   certificate then relates to the code. The kernel's replay re-derives a
    ///   δβ-step by the same saturated substitution, so a lambda chain is
    ///   consumed whole or not at all, as an operator of as many parameters.
    /// - fails: [`CheckRefusal::DanglingNode`] for a node `core` does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::DanglingNode`] — a node does not resolve.
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
    ///   further argument, and a rigid head.
    /// - witness: `code::tests::a_static_step_reduces_saturated_instances_and_redexes_only`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(step)) => step.redex() == code && match step.unfolded() {
            | Unfolded::Definition(constant) => matches!(self.body(constant), Maybe::Present(_)),
            | Unfolded::Abstraction(head) => matches!(core.value(head), Some(Value::StaticLambda(_))),
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
            | Value::StaticLambda(_) => (Unfolded::Abstraction(head), head),
            | Value::Constant(constant) => {
                let Maybe::Present(body) = self.body(constant)
                else {
                    return rigid;
                };
                (Unfolded::Definition(constant), body)
            },
            | Value::PathRefl(_)
            | Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
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

    /// Certify that the step `step` took holds: its redex converts to its
    /// reduct.
    ///
    /// # Specification
    /// - requires: `step` is a reduction [`Self::reduce`] gave over `core`;
    ///   every body this table holds lives in `core`.
    /// - ensures: the certificate of the machine's verdict on the redex against
    ///   the reduct, each evaluated with the free binders the redex reaches
    ///   read as rigid variables — the reduct reaches no further — the
    ///   derivation a recording sink kept.
    /// - provides: the one route by which a code position reduces, and the
    ///   trace the kernel's replay re-derives.
    /// - fails: [`CheckRefusal::Undecided`] at `redex` when either side does
    ///   not evaluate, the machine faults, or its verdict is anything but
    ///   convertible.
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
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Ok(ref certificate) => {
            certificate.unfolded() == step.unfolded()
                && certificate.redex() == step.redex()
                && certificate.reduct() == step.reduct()
                && certificate.verdict() == MachineVerdict::Convertible
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
            | MachineVerdict::Convertible => Ok(Certificate {
                unfolded: step.unfolded,
                redex: step.redex,
                reduct: step.reduct,
                verdict: report.verdict(),
                decisions: log.decisions().copied().collect(),
            }),
            | MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => Err(undecided),
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
        Ok(match report.verdict() {
            | MachineVerdict::Convertible => Maybe::Present(log.decisions().copied().collect()),
            | MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => {
                Maybe::Absent(converted::Absent::Apart)
            },
        })
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
    /// # Termination
    /// - reason: the `for` loop binds one rigid variable per open binder, not
    ///   recursion; the machine runs under its own fuel.
    /// - measure: the binders left to bind.
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
                .map_err(|_fault| undecided)?;
            let bound = domain
                .value_neutral(neutral, TermFace::Reduced)
                .map_err(|_fault| undecided)?;
            environment.extend(Zone::Intuitionistic, bound);
        }
        let fuel = Fuel::from(CODE_FUEL);
        let evaluate = |domain: &mut DomainArena, term: ComputationId| {
            gandr_core_nbe::eval_comp_within(
                core,
                domain,
                definitions,
                fuel,
                term,
                environment.clone(),
            )
            .map(|(produced, _remaining)| produced)
            .map_err(|_fault| undecided)
        };
        let one = evaluate(&mut domain, left)?;
        let other = evaluate(&mut domain, right)?;
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
            | MachineVerdict::Convertible => Maybe::Present(
                log.decisions()
                    .copied()
                    .map(|decision| decision.map(|_anchor| ()))
                    .collect(),
            ),
            | MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => {
                Maybe::Absent(converted::Absent::Apart)
            },
        })
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
        let Readback::Returned { normal, returned } = self.read_back(core, claim)?
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
        match self.read_back(core, claim)? {
            | Readback::Returned { normal, returned } => {
                let decisions = self.claim_trace(core, claim, normal)?;
                Ok(Reading::Returned(Evaluation {
                    normal,
                    returned,
                    decisions,
                }))
            },
            | Readback::Stuck(normal) => {
                let decisions = self.claim_trace(core, claim, normal)?;
                Ok(Reading::Stuck(Stalled { normal, decisions }))
            },
            | Readback::Unsuspended => Err(CheckRefusal::Undecided { at: claim }),
        }
    }

    /// Read the closed claim `claim` back, round by round, until its body
    /// returns or a round changes nothing.
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
    ) -> Result<Readback, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: claim };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
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
    /// normal form `normal`.
    ///
    /// # Specification
    /// - requires: as [`Self::evaluate_claim`]; `normal` is the claim's
    ///   readback.
    /// - ensures: the decisions the machine recorded converting the two, in
    ///   order.
    /// - fails: [`CheckRefusal::Undecided`] at `claim` when either side does
    ///   not evaluate or the machine does not convert them.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::evaluate_claim`] and [`Self::read_claim`].
    /// - witness: `bridge::tests::a_funext_crosses_as_a_higher_evaluation`
    /// - witness: `bridge::tests::a_quantified_funext_crosses_as_a_quantified_evaluation`
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
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
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
            | CoreNode::Term(TermNode::Value(at)) => {
                match *core.value(at).ok_or_else(|| dangling(node))? {
                    | Value::Constructor {
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
                    | Value::Record(ref fields) => work.extend(
                        fields
                            .values()
                            .map(|&field| (CoreNode::Term(TermNode::Value(field)), depth)),
                    ),
                    | Value::Reify(ref frames) => {
                        for frame in frames.iter() {
                            match *frame {
                                | gandr_core_term::control::StackFrame::Apply(value) => {
                                    work.push((CoreNode::Term(TermNode::Value(value)), depth));
                                },
                                | gandr_core_term::control::StackFrame::Bind(body) => {
                                    work.push((CoreNode::Term(TermNode::Computation(body)), under));
                                },
                                | gandr_core_term::control::StackFrame::Project(_) => {},
                            }
                        }
                    },
                    | Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ..
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(path_type)), depth));
                        work.push((CoreNode::Term(TermNode::Value(forward)), depth));
                        work.push((CoreNode::Term(TermNode::Value(backward)), depth));
                    },
                    | Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    } => {
                        let outside = usize::try_from(u32::from(index))
                            .ok()
                            .and_then(|counted| counted.checked_add(1))
                            .ok_or(CheckRefusal::MachineInvariant)?;
                        reach = reach.max(outside.saturating_sub(depth));
                    },
                    | Value::Primitive { .. }
                    | Value::Variable {
                        zone: Zone::Linear, ..
                    }
                    | Value::Constant(_)
                    | Value::ListNil
                    | Value::Literal(_)
                    | Value::Hole(_) => {},
                    | Value::Tuple(ref components) => work.extend(
                        components
                            .iter()
                            .map(|&component| (CoreNode::Term(TermNode::Value(component)), depth)),
                    ),
                    | Value::PathProduct(first, second)
                    | Value::Funext(first, second)
                    | Value::Equiv(first, second)
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
                    | Value::PathRefl(body)
                    | Value::Here(body)
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. }
                    | Value::Mark { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(body)), depth));
                    },
                    | Value::StaticLambda(body) => {
                        work.push((CoreNode::Term(TermNode::Value(body)), under));
                    },
                    | Value::Thunk(body)
                    | Value::Returned(body)
                    | Value::Nested(body)
                    | Value::Run(body) => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), depth));
                    },
                    | Value::Quote(quoted) => {
                        work.push((CoreNode::Type(TypeNode::Value(quoted)), depth));
                    },
                    | Value::QuoteComputation(quoted) => {
                        work.push((CoreNode::Type(TypeNode::Computation(quoted)), depth));
                    },
                }
            },
            | CoreNode::Term(TermNode::Computation(at)) => {
                match *core.computation(at).ok_or_else(|| dangling(node))? {
                    | Computation::DataCase {
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
                    | Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _) => {
                        work.push((CoreNode::Term(TermNode::Value(record)), depth));
                    },
                    | Computation::Split {
                        scrutinee,
                        arity,
                        body,
                    } => {
                        let inside = depth
                            .checked_add(usize::from(arity))
                            .ok_or(CheckRefusal::MachineInvariant)?;
                        work.push((CoreNode::Term(TermNode::Value(scrutinee)), depth));
                        work.push((CoreNode::Term(TermNode::Computation(body)), inside));
                    },
                    | Computation::Perform {
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
                    | Computation::Exercise {
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
                    | Computation::Scope {
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
                    | Computation::Handle {
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
                    | Computation::Resume(stack, body) => work.extend([
                        (CoreNode::Term(TermNode::Value(stack)), depth),
                        (CoreNode::Term(TermNode::Computation(body)), depth),
                    ]),
                    | Computation::With(first, second) => work.extend([
                        (CoreNode::Term(TermNode::Computation(first)), depth),
                        (CoreNode::Term(TermNode::Computation(second)), depth),
                    ]),
                    | Computation::Reset(body)
                    | Computation::Project(_, body)
                    | Computation::Mark { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), depth));
                    },
                    | Computation::Shift(body)
                    | Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), under));
                    },
                    | Computation::ListFold {
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
                    | Computation::Primitive { arguments, .. } => {
                        work.extend(
                            arguments.iter().map(|argument| {
                                (CoreNode::Term(TermNode::Value(*argument)), depth)
                            }),
                        );
                    },
                    | Computation::Transport(path, value) => {
                        work.push((CoreNode::Term(TermNode::Value(path)), depth));
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    | Computation::PathTransport {
                        motive,
                        path,
                        value,
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(motive)), under));
                        work.push((CoreNode::Term(TermNode::Value(path)), depth));
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    | Computation::TelescopeTransport {
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
                    | Computation::Application(head, argument) => {
                        work.push((CoreNode::Term(TermNode::Computation(head)), depth));
                        work.push((CoreNode::Term(TermNode::Value(argument)), depth));
                    },
                    | Computation::Return(value) | Computation::Force(value) => {
                        work.push((CoreNode::Term(TermNode::Value(value)), depth));
                    },
                    | Computation::Bind(bound, body) => {
                        work.push((CoreNode::Term(TermNode::Computation(bound)), depth));
                        work.push((CoreNode::Term(TermNode::Computation(body)), under));
                    },
                    | Computation::Case {
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
                    | Computation::Session(ref action) => {
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
                    | Computation::Hole(_) => {},
                }
            },
            | CoreNode::Type(TypeNode::Value(at)) => {
                match *core.value_type(at).ok_or_else(|| dangling(node))? {
                    | ValueType::Data { ref arguments, .. } => work.extend(
                        arguments
                            .iter()
                            .map(|&argument| (CoreNode::Term(TermNode::Value(argument)), depth)),
                    ),
                    | ValueType::Record(ref fields) => work.extend(
                        fields
                            .values()
                            .map(|&field| (CoreNode::Type(TypeNode::Value(field)), depth)),
                    ),
                    | ValueType::Stack { input, output } => work.extend([
                        (CoreNode::Type(TypeNode::Computation(input)), depth),
                        (CoreNode::Type(TypeNode::Computation(output)), depth),
                    ]),
                    | ValueType::PathUniverse(source, target) => {
                        work.push((CoreNode::Term(TermNode::Value(source)), depth));
                        work.push((CoreNode::Term(TermNode::Value(target)), depth));
                    },
                    | ValueType::Path {
                        carrier,
                        left,
                        right,
                    } => work.extend([
                        (CoreNode::Type(TypeNode::Value(carrier)), depth),
                        (CoreNode::Term(TermNode::Value(left)), depth),
                        (CoreNode::Term(TermNode::Value(right)), depth),
                    ]),
                    | ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                        work.extend(
                            parts
                                .iter()
                                .map(|&part| (CoreNode::Type(TypeNode::Value(part)), depth)),
                        );
                    },
                    | ValueType::Session(ref session) => {
                        work.extend(
                            session
                                .payloads()
                                .iter()
                                .map(|&payload| (CoreNode::Type(TypeNode::Value(payload)), depth)),
                        );
                    },
                    | ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown => {},
                    | ValueType::Capability { ref authority, .. } => work.extend(
                        authority
                            .types()
                            .map(|ty| (CoreNode::Type(TypeNode::Value(ty)), depth)),
                    ),
                    | ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    } => {
                        work.push((CoreNode::Type(TypeNode::Value(first)), depth));
                        work.push((CoreNode::Type(TypeNode::Value(second)), depth));
                    },
                    | ValueType::Thunk(body) => {
                        work.push((CoreNode::Type(TypeNode::Computation(body)), depth));
                    },
                    | ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                        work.push((CoreNode::Type(TypeNode::Value(inner)), depth));
                    },
                    | ValueType::Element { code, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(code)), depth));
                    },
                }
            },
            | CoreNode::Type(TypeNode::Computation(at)) => {
                match *core.comp_type(at).ok_or_else(|| dangling(node))? {
                    | CompType::With(first, second) => work.extend([
                        (CoreNode::Type(TypeNode::Computation(first)), depth),
                        (CoreNode::Type(TypeNode::Computation(second)), depth),
                    ]),
                    | CompType::Returner {
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
                    | CompType::Arrow { domain, codomain } => {
                        work.push((CoreNode::Type(TypeNode::Value(domain)), depth));
                        work.push((CoreNode::Type(TypeNode::Computation(codomain)), depth));
                    },
                    | CompType::Pi { domain, codomain } => {
                        work.push((CoreNode::Type(TypeNode::Value(domain)), depth));
                        work.push((CoreNode::Type(TypeNode::Computation(codomain)), under));
                    },
                    | CompType::Element { code, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(code)), depth));
                    },
                    | CompType::Unknown => {},
                }
            },
        }
    }
    Ok(BinderDepth::from(reach))
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use quenchant_shape::shape::Maybe;

    use super::CodeDefinitions;
    use super::CoreNode;
    use super::TermNode;
    use super::TypeNode;
    use super::Unfolded;
    use super::loose_reach;
    use super::unfolding;

    /// The two atoms `reduct`, a quote of a product, pairs.
    ///
    /// # Specification
    /// - requires: `reduct` quotes a product whose two children resolve.
    /// - ensures: the two stored children are returned in product order.
    /// - panics: the recipe did not produce such a quote.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-argument static operator receives distinct type
    ///   codes, and its quoted product is asserted in argument order; this
    ///   separates swapped substitution and wrong quoted children.
    /// - witness: `code::tests::a_static_step_reduces_saturated_instances_and_redexes_only`
    #[spec(ensures: |ret| matches!(arena.value(reduct), Some(Value::Quote(quoted))
        if arena.value_type(*quoted).is_some_and(|held| matches!(*held, ValueType::Product(ref parts)
            if matches!(**parts, [first, second] if arena.value_type(first) == Some(&ret.0) && arena.value_type(second) == Some(&ret.1))))))]
    fn quoted_pair(
        arena: &CoreArena,
        reduct: ValueId,
    ) -> (ValueType, ValueType)
    {
        let Some(&Value::Quote(quoted)) = arena.value(reduct)
        else {
            panic!("the reduct is a quote: {:?}", arena.value(reduct));
        };
        let Some(held) = arena.value_type(quoted)
        else {
            panic!("the quote holds a product");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("the quote holds a product");
        };
        let [first, second] = **parts
        else {
            panic!("the quoted product is binary");
        };
        (
            arena.value_type(first).cloned().unwrap(),
            arena.value_type(second).cloned().unwrap(),
        )
    }

    #[test]
    fn a_static_step_reduces_saturated_instances_and_redexes_only()
    {
        // def Num : Type = Integer ;
        // def Both : Type -> Type -> Type = \A. \B. El A * El B ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let num_body = arena.value_quote(integer);
        let integer_code = arena.value_quote(integer);
        let string_code = arena.value_quote(string);
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let first = arena.value_type_element(outer, Level::zero());
        let second = arena.value_type_element(inner, Level::zero());
        let product = arena.value_type_product(&[first, second]);
        let quoted = arena.value_quote(product);
        let inner_lambda = arena.value_static_lambda(quoted);
        let both_body = arena.value_static_lambda(inner_lambda);
        let mut definitions = CodeDefinitions::new();
        definitions.define(ConstantIndex::from(0_usize), num_body);
        definitions.define(ConstantIndex::from(1_usize), both_body);
        let num = arena.value_constant(ConstantIndex::from(0_usize));
        let both = arena.value_constant(ConstantIndex::from(1_usize));
        let partial = arena.value_static_application(both, integer_code);
        let saturated = arena.value_static_application(partial, string_code);
        let further = arena.value_static_application(saturated, integer_code);
        let num_applied = arena.value_static_application(num, string_code);
        let redex = arena.value_static_application(inner_lambda, string_code);
        let short = arena.value_static_application(both_body, integer_code);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let rigid = arena.value_static_application(bound, integer_code);
        let unknown = arena.value_constant(ConstantIndex::from(5_usize));

        let step =
            |arena: &mut CoreArena, code: ValueId| match definitions.reduce(arena, code).unwrap() {
                | Maybe::Present(step) => {
                    assert_eq!(step.redex(), code, "a step fires at the code itself");
                    Maybe::Present((step.unfolded(), step.reduct()))
                },
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
        let defined = |position: usize| Unfolded::Definition(ConstantIndex::from(position));

        assert_eq!(
            step(&mut arena, num),
            Maybe::Present((defined(0), num_body)),
            "a constant with a body unfolds to that body"
        );
        let Maybe::Present((unfolded, reduct)) = step(&mut arena, saturated)
        else {
            panic!("a saturated instance reduces");
        };
        assert_eq!(unfolded, defined(1), "the instance unfolds its definition");
        assert_eq!(
            quoted_pair(&arena, reduct),
            (
                ValueType::Base(BaseType::Integer),
                ValueType::Base(BaseType::String)
            ),
            "the arguments instantiate the parameters outermost first, decoded on mint"
        );
        let Maybe::Present((unfolded, reduct)) = step(&mut arena, further)
        else {
            panic!("an instance under a further argument reduces");
        };
        let Some(&Value::StaticApplication(applied, argument)) = arena.value(reduct)
        else {
            panic!("the reduct stays applied to the argument the operator does not take");
        };
        assert_eq!(
            (unfolded, argument, quoted_pair(&arena, applied).1),
            (defined(1), integer_code, ValueType::Base(BaseType::String)),
            "the operator consumes its two parameters and re-applies the third argument"
        );
        let Maybe::Present((unfolded, reduct)) = step(&mut arena, num_applied)
        else {
            panic!("a nullary definition under an argument reduces");
        };
        assert_eq!(
            (unfolded, arena.value(reduct).cloned()),
            (
                defined(0),
                Some(Value::StaticApplication(num_body, string_code))
            ),
            "a body of no parameters stands under every argument"
        );
        let Maybe::Present((unfolded, reduct)) = step(&mut arena, redex)
        else {
            panic!("a saturated static redex reduces");
        };
        assert_eq!(
            (unfolded, quoted_pair(&arena, reduct).1),
            (
                Unfolded::Abstraction(inner_lambda),
                ValueType::Base(BaseType::String)
            ),
            "a static redex unfolds the abstraction at its head"
        );
        for code in [partial, short, rigid, unknown] {
            assert_eq!(
                step(&mut arena, code),
                Maybe::Absent(unfolding::Absent::Rigid),
                "an operator short of its arguments, a variable head and a constant without a \
                 body are rigid"
            );
        }
    }

    #[test]
    fn the_loose_reach_counts_only_binders_outside_the_root()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let closed = arena.value_quote(integer);
        let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let two = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(4_u32));
        let bound_inside = arena.value_static_lambda(zero);
        let reaching_out = arena.value_static_lambda(two);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let decoded = arena.value_type_element(one, Level::zero());
        let returns = arena.comp_type_returner(decoded);
        let dependent = arena.comp_type_pi(small, returns);
        let under_pi = arena.value_quote_computation(dependent);
        let decoded_domain = arena.value_type_element(zero, Level::zero());
        let returns_unit = arena.comp_type_returner(unit);
        let in_domain = arena.comp_type_pi(decoded_domain, returns_unit);
        let domain_quote = arena.value_quote_computation(in_domain);
        let path_at_variable = arena.value_type_path(decoded, zero, zero);
        let value = |at| CoreNode::Term(TermNode::Value(at));
        let rows = [
            (value(closed), 0_usize, "a closed code reaches nothing"),
            (
                value(two),
                3_usize,
                "a bare variable reaches one past its index",
            ),
            (value(linear), 0_usize, "a linear variable counts no binder"),
            (
                value(bound_inside),
                0_usize,
                "a variable its own lambda binds reaches nothing",
            ),
            (
                value(reaching_out),
                2_usize,
                "a lambda's binder is subtracted from its body's reach",
            ),
            (
                value(under_pi),
                1_usize,
                "a dependent codomain's binder is subtracted",
            ),
            (
                value(domain_quote),
                1_usize,
                "a dependent domain sits outside the binder",
            ),
            (
                CoreNode::Type(TypeNode::Value(path_at_variable)),
                2_usize,
                "a type reaches through the decode at its carrier",
            ),
        ];
        for (root, reach, message) in rows {
            assert_eq!(
                loose_reach(&arena, root),
                Ok(BinderDepth::from(reach)),
                "{message}"
            );
        }
    }

    #[test]
    fn definitions_reject_reordering_without_replacing_earlier_bodies()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let original = arena.value_quote(integer);
        let replacement = arena.value_quote(string);
        let first = ConstantIndex::from(2_usize);
        let earlier = ConstantIndex::from(1_usize);
        let later = ConstantIndex::from(4_usize);
        let reference = arena.value_constant(first);
        let mut definitions = CodeDefinitions::new();
        definitions.define(first, original);
        definitions.define(first, replacement);
        definitions.define(earlier, replacement);
        definitions.define(later, replacement);
        assert_eq!(definitions.body(first), Maybe::Present(original));
        assert_eq!(
            definitions.body(earlier),
            Maybe::Absent(unfolding::Absent::Rigid)
        );
        assert_eq!(definitions.body(later), Maybe::Present(replacement));
        let Maybe::Present(step) = definitions.reduce(&mut arena, reference).unwrap()
        else {
            panic!("the retained definition still unfolds");
        };
        assert_eq!(step.reduct(), original);
        let certificate = definitions.certify(&arena, step).unwrap();
        assert_eq!(certificate.reduct(), original);
        assert_eq!(
            certificate.verdict(),
            gandr_core_nbe::MachineVerdict::Convertible
        );
    }
}
