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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::BinderLevel;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Environment;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ResharingMemo;
use gandr_core_nbe::TermFace;
use gandr_core_nbe::TraceNode;
use gandr_core_nbe::Unfolding;
use gandr_core_nbe::decide;
use gandr_core_nbe::eval_value_within;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_value;
use gandr_kernel_conversion_trace::ConversionDecision;
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

/// The evaluation budget each side of a certified unfolding runs under.
const CODE_FUEL: u32 = 4_096_u32;

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
        let mut chain = self.lowered.chain().clone();
        if chain
            .define(
                constant,
                GlobalIndex::from(entry),
                Transparency::Manifest,
                &[],
            )
            .is_err()
        {
            return;
        }
        let mut bodies = self.bodies.clone();
        bodies.insert(constant, body);
        let lowered = LoweredChain::lower(chain, |defined| {
            bodies
                .get(&defined.constant())
                .copied()
                .ok_or_else(|| defined.constant())
        });
        if let Ok(lowered) = lowered {
            self.lowered = lowered;
            self.bodies = bodies;
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
            | Value::Primitive { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Variable { .. }
            | Value::Unit
            | Value::Literal(_)
            | Value::Pair(..)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..) => return rigid,
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
        let open = u32::try_from(usize::from(loose_reach(core, step.redex)?))
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
}

/// How many binders outside `root` its free intuitionistic variables reach:
/// one past the largest index that counts out of every binder within `root`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: zero for a closed value; otherwise the least `n` such that `root`
///   read beneath `n` binders mentions no binder beyond them. Linear variables
///   count no binder and reach nothing.
/// - provides: the environment a certificate evaluates an open code in.
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
///   beneath a static lambda, and a variable beneath a dependent arrow's binder
///   inside a quote, each reach asserted.
/// - witness: `code::tests::the_loose_reach_counts_only_binders_outside_the_root`
#[inline]
#[spec(ensures: |ret| match (core.value(root), ret) {
    | (Some(&Value::Variable { zone: Zone::Intuitionistic, index }), Ok(reach)) => {
        usize::try_from(u32::from(index)).ok().and_then(|counted| counted.checked_add(1))
            == Some(usize::from(reach))
    },
    | (Some(&(Value::Constant(_) | Value::Unit | Value::Literal(_))), Ok(reach)) => {
        reach == BinderDepth::default()
    },
    | _ => true,
})]
pub fn loose_reach(
    core: &CoreArena,
    root: ValueId,
) -> Result<BinderDepth, CheckRefusal>
{
    let dangling = |node| CheckRefusal::DanglingNode { node };
    let mut reach = 0_usize;
    let mut work = Vec::from([(CoreNode::Term(TermNode::Value(root)), 0_usize)]);
    while let Some((node, depth)) = work.pop() {
        let under = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        match node {
            | CoreNode::Term(TermNode::Value(at)) => {
                match *core.value(at).ok_or_else(|| dangling(node))? {
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
                    | Value::Unit
                    | Value::Literal(_) => {},
                    | Value::PathProduct(first, second)
                    | Value::Pair(first, second)
                    | Value::StaticApplication(first, second) => {
                        work.push((CoreNode::Term(TermNode::Value(first)), depth));
                        work.push((CoreNode::Term(TermNode::Value(second)), depth));
                    },
                    | Value::PathRefl(body)
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(body)), depth));
                    },
                    | Value::StaticLambda(body) => {
                        work.push((CoreNode::Term(TermNode::Value(body)), under));
                    },
                    | Value::Thunk(body) => {
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
                    | Computation::Lambda(body) => {
                        work.push((CoreNode::Term(TermNode::Computation(body)), under));
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
                        on_left,
                        on_right,
                    } => {
                        work.push((CoreNode::Term(TermNode::Value(scrutinee)), depth));
                        work.push((CoreNode::Term(TermNode::Computation(on_left)), under));
                        work.push((CoreNode::Term(TermNode::Computation(on_right)), under));
                    },
                }
            },
            | CoreNode::Type(TypeNode::Value(at)) => {
                match *core.value_type(at).ok_or_else(|| dangling(node))? {
                    | ValueType::PathUniverse(source, target) => {
                        work.push((CoreNode::Term(TermNode::Value(source)), depth));
                        work.push((CoreNode::Term(TermNode::Value(target)), depth));
                    },
                    | ValueType::Base(_)
                    | ValueType::Unit
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_) => {},
                    | ValueType::Product(first, second)
                    | ValueType::Sum(first, second)
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
                    | ValueType::Lift { inner, .. } => {
                        work.push((CoreNode::Type(TypeNode::Value(inner)), depth));
                    },
                    | ValueType::Element { code, .. } => {
                        work.push((CoreNode::Term(TermNode::Value(code)), depth));
                    },
                }
            },
            | CoreNode::Type(TypeNode::Computation(at)) => {
                match *core.comp_type(at).ok_or_else(|| dangling(node))? {
                    | CompType::Returner(result) => {
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
        if matches!(arena.value_type(*quoted), Some(ValueType::Product(first, second))
            if arena.value_type(*first) == Some(&ret.0) && arena.value_type(*second) == Some(&ret.1))))]
    fn quoted_pair(
        arena: &CoreArena,
        reduct: ValueId,
    ) -> (ValueType, ValueType)
    {
        let Some(&Value::Quote(quoted)) = arena.value(reduct)
        else {
            panic!("the reduct is a quote: {:?}", arena.value(reduct));
        };
        let Some(&ValueType::Product(first, second)) = arena.value_type(quoted)
        else {
            panic!("the quote holds a product");
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
        let product = arena.value_type_product(first, second);
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
        let rows = [
            (closed, 0_usize, "a closed code reaches nothing"),
            (two, 3_usize, "a bare variable reaches one past its index"),
            (linear, 0_usize, "a linear variable counts no binder"),
            (
                bound_inside,
                0_usize,
                "a variable its own lambda binds reaches nothing",
            ),
            (
                reaching_out,
                2_usize,
                "a lambda's binder is subtracted from its body's reach",
            ),
            (
                under_pi,
                1_usize,
                "a dependent codomain's binder is subtracted",
            ),
            (
                domain_quote,
                1_usize,
                "a dependent domain sits outside the binder",
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
