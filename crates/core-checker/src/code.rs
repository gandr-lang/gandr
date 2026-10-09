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

use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ResharingMemo;
use gandr_core_nbe::TraceNode;
use gandr_core_nbe::decide;
use gandr_core_nbe::eval_value;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::ValueId;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;
use quenchant_shape::shape::Maybe;

use crate::refusal::CheckRefusal;

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
    /// trivial.
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

/// The normaliser's certificate that a code constant converts to its body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Certificate
{
    /// The constant unfolded.
    constant: ConstantIndex,
    /// The body it unfolded to.
    body: ValueId,
    /// The machine's verdict.
    verdict: MachineVerdict,
    /// The derivation the machine recorded, in order.
    decisions: Vec<ConversionDecision<TraceNode>>,
}

impl Certificate
{
    /// The constant unfolded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The body it unfolded to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> ValueId
    {
        self.body
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
    ///   follows every position recorded before it; a position out of order, or
    ///   past the chain's entry space, is left rigid, which costs a later
    ///   unfolding and never soundness.
    /// - panics: none.
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

    /// Certify that the constant `code` names converts to its body.
    ///
    /// # Specification
    /// - requires: `code` is a constant of `core` whose position this table
    ///   holds a body for, and every body lives in `core`.
    /// - ensures: the certificate of the machine's verdict on the constant
    ///   against its body, with the derivation a recording sink kept.
    /// - provides: the one route by which a code position reduces, and the
    ///   trace the kernel's replay re-derives.
    /// - fails: [`CheckRefusal::Undecided`] at `code` when either side does not
    ///   evaluate, the machine faults, or its verdict is anything but
    ///   convertible.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::Undecided`] — the unfolding was not certified.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the kernel's replay is the external oracle: every
    ///   certificate a readmission records over generated code constants
    ///   replays to convertible; the L3 residue is a body chained through a
    ///   second constant and a corrupted trace refused.
    /// - witness: `bridge::tests::a_code_constant_unfolds_in_conversion_and_its_trace_replays`
    /// - witness: `bridge::tests::every_readmission_certificate_replays`
    /// - witness: `bridge::tests::a_declining_certificate_faults_the_declaration`
    #[inline]
    pub fn certify(
        &self,
        core: &CoreArena,
        code: ValueId,
        constant: ConstantIndex,
    ) -> Result<Certificate, CheckRefusal>
    {
        let undecided = CheckRefusal::Undecided { at: code };
        let Maybe::Present(body) = self.body(constant)
        else {
            return Err(undecided);
        };
        let definitions =
            Definitions::new(&self.lowered, &self.environment, self.environment.root());
        let mut domain = DomainArena::new();
        let fuel = Fuel::from(CODE_FUEL);
        let left =
            eval_value(core, &mut domain, definitions, fuel, code).map_err(|_fault| undecided)?;
        let right =
            eval_value(core, &mut domain, definitions, fuel, body).map_err(|_fault| undecided)?;
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
        match report.verdict() {
            | MachineVerdict::Convertible => Ok(Certificate {
                constant,
                body,
                verdict: report.verdict(),
                decisions: log.decisions().copied().collect(),
            }),
            | MachineVerdict::NotConvertible | MachineVerdict::Declined(_) => Err(undecided),
        }
    }
}
