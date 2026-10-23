//! The one composition: parse, lower, adapt, check, settle.
//!
//! # One lowering, one verdict set
//!
//! Every source is lowered exactly once per run, under one strictness, and
//! every declaration gets one verdict: the checker's, settled against what the
//! declaration states. The one call into the lowering sits in a private module
//! that counts each source it lowers, and [`LoweringCount`] is the projection
//! through which a run shows it lowered each source once.
//!
//! # A component is composed once
//!
//! Sources joined by path imports are composed as the unit the `component`
//! module lays out — the import-connected component, its sources in
//! dependency order — lowered into one arena, checked against one
//! environment, settled once and admitted once, each source's certificate
//! replayed in that order. [`judge_component`] then projects the one
//! composition onto each source: each reports its own declarations, refusals,
//! shadowed builtins, inferred exits and runs, uses of deprecated
//! declarations and the obligations its declarations owe, and shares the
//! component's origins, failures, program and kernel artifact. A source given
//! alone is composed over its import closure, its own text last
//! ([`judge_member`]), which is the component it makes on its own: the
//! session's unit.
//!
//! - Recorded design: one arena and one kernel environment per import-connected
//!   component, its members in dependency order, each lowered and checked once
//!   and its export the importer's prefix by constant, components with no
//!   import between them on the pool's threads.
//! - Departure: the members of one level of the import graph lower one after
//!   another rather than in parallel, since the lowering reads one tree; the
//!   `component` module states it with its reversal.
//! - A whole-component refusal, a parse fault, a settle fault and a kernel
//!   disagreement are each every member's: none leaves a composition to
//!   project. A kernel disagreement is an engine fault, never a verdict about a
//!   source.
//!
//! Witness: `walk::tests::an_importer_is_judged_over_its_sibling` — a diamond
//! of four sources and a source beside it are lowered as two components, each
//! source counted once among the lowerings; each source reports its own
//! declarations alone, and each certificate holds the base's segments once,
//! first.
//!
//! # The kernel re-derives every acceptance
//!
//! After the checker judges a module, the kernel is offered every declaration
//! it accepted. A declaration the kernel does not re-derive is a disagreement
//! between the two checkers — an engine fault, never a verdict about the
//! author's source. What crossed is exported once, as the kernel artifact a
//! settled composition carries, each declaration under its structured name.
//!
//! After the checker judges a module, every declaration it accepted is offered
//! to the kernel through the checker's bridge. A declaration the kernel
//! rejects, or one the bridge refuses for any reason but a reference to a
//! declaration that did not cross or an effectful former, is
//! `ComposeFault::Readmission`: a disagreement between the two checkers is an
//! engine fault, exit `2`, never a verdict about the author's source. A
//! refused declaration crosses as its mark and a reference to it is withheld,
//! and neither is a disagreement.
//!
//! An effectful declaration — one holding an effect row, a capability, an
//! exercise, a scope or any other control former — stays on the checker's
//! side: the kernel is pure and has no rule for them by design, so the
//! bridge's refusal by that former's name is the expected answer rather than
//! a disagreement, and what names the declaration is withheld. A pure former
//! the bridge refuses remains a fault. Reversal: when the kernel admits
//! effectful computations.
//!
//! This goes beyond the slice's plan, which settles the checker's verdicts
//! alone. The kernel is the oracle the checker answers to, and the readmission
//! costs one erasure per accepted declaration; running it on the pass that
//! gates means no acceptance a run reports is the untrusted checker's word
//! alone. The choice reverses if readmission's cost dominates a run, at which
//! point it moves behind a flag that the gate still sets.
//!
//! What crossed is exported once on the same pass: `Composed::Settled` carries
//! `kernel`, the canonical artifact of every declaration that crossed, in
//! kernel admission order and under the module's structured names, so a caller
//! that persists the kernel environment — the session's kernel checkpoint —
//! never readmits the module itself. The export is one encoding of an
//! environment the readmission already built. The alternative was carrying the
//! readmission and leaving the export to a caller, which would make every
//! caller own the name table and the encoding call. The choice reverses if the
//! export's cost shows in a run that never reads it.
//!
//! **The admission can follow the report.** `judge` checks the module, builds
//! its program and settles its verdicts, and returns them as `Judged` beside
//! the module's `Admission`: the checker's arena, its verdicts and the
//! structured names. `Admission::admit` readmits and exports, and
//! `Judged::admit` completes the composition with the artifact. A disagreement
//! outranks a settle fault there, as it does in `judge_module`. The settle
//! comparison reads only the checker's verdicts, so a module settled before its
//! admission settles to the report one settled after it gives;
//! `a_judged_module_renders_before_its_admission` compares the two orders. The
//! readmission and the export are linear in the module and the judgement of an
//! edited revision need not be, so an interactive caller renders the report
//! first and admits after. The batch verbs gate on the admission and keep
//! `judge_module`. The split reverses if the settle comparison comes to read
//! anything the readmission mints.
//!
//! # The admission runs after the composition is read
//!
//! [`judge`] checks, focuses and settles a module and returns the settled
//! composition beside the [`Admission`] still to run: the arena it was judged
//! over, the verdicts and the names the export writes. Nothing the settle
//! comparison or the program reads is minted by the readmission, so a face
//! renders the composition's reports before the kernel has been offered
//! anything, and the kernel artifact joins the composition when the admission
//! completes ([`Judged::admit`]). [`judge_module`] is the two in sequence, and
//! a kernel disagreement takes precedence over a settle fault, as it did when
//! the readmission ran first.
//!
//! # A second-run refusal is published at the written node that elaborated
//!
//! A body holding a computation written where a value is read is judged
//! twice, and the verdict, a refusal and every frame it names come from the
//! second run, over the body the checker elaborated: nodes the lowering never
//! minted. `judge` gives each of them the origin of the written node it
//! elaborates before the composition is read: a rebuilt node the origin of
//! the node it was rebuilt from, so the respect check of a case whose arms
//! nest a call refuses at the case block as the bound spelling does, and a
//! bind minted for a run the origin of the nested call it runs. The table is
//! the lowering's, extended, so every face reading the composition — the
//! terminal, the language server — locates the refusal alike. The alternative
//! was a refusal that names the file alone, which an editor publishes nowhere.
//! The carriage retires with the second run, whose reversal the checker's
//! `nested` module names.
//!
//! # One composition serves both verbs
//!
//! `check` and `test` run the same walk and the same `compose`; they differ
//! only in what `shown` prints and in what `--goals` does to the gate. A source
//! is lowered exactly once per run, under one strictness, and each declaration
//! gets exactly one verdict: the checker's, settled against what it states.
//! `RunReport::lowerings` counts every source the crate lowers, and the corpus
//! suite asserts it equals the number of sources read. `run` composes
//! its one source through the same `compose`, under the root its path
//! classifies as.
//!
//! The alternative was a total session pass and a separate strict tier over the
//! same sources, which lowers each source twice and gives each declaration two
//! verdicts that can disagree. The choice reverses only if a verb needs a
//! different lowering of the same source, which would arrive as a parameter of
//! the one composition rather than a second one.
//!
//! The session (`gandr-surface-session`) is the one other caller. It runs the
//! same two halves `compose` runs — the lowering, then `judge` with the
//! `Admission` it leaves run after the face renders — and keeps the lowered
//! module between them to hand the incremental checker, so a submission's
//! verdicts are this composition's and the corpus agreement suite there
//! compares them source by source. It parses through its own form store, which
//! takes up the forms an edit left unchanged, and lowers that parse with
//! `lower_parsed`, the lowering half of `lower_source` past its parse; the
//! parse it hands over equals `parse` of the same text, so the lowering is the
//! one `compose` runs. The halves are public rather than duplicated there
//! because a second composition is exactly what this section rules out.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use core::fmt;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_checker::AbstractType;
use gandr_core_checker::AtomInterface;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Checkpoint;
use gandr_core_checker::ComponentOrdinal;
use gandr_core_checker::Declaration;
use gandr_core_checker::Demand;
use gandr_core_checker::Formations;
use gandr_core_checker::HostGrant;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::ModuleRun;
use gandr_core_checker::Nesting;
use gandr_core_checker::ObligationCount;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::SealSite;
use gandr_core_checker::SealingSite;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Unretired;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_checker::worlds::Entry;
use gandr_core_checker::worlds::HostEntry;
use gandr_core_checker::worlds::Mobility;
use gandr_core_checker::worlds::WorldName;
use gandr_core_term::Carried;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::StructuredName;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Produced;
use gandr_surface_corpus::SettleFault;
use gandr_surface_corpus::SettleReport;
use gandr_surface_corpus::settle;
use gandr_surface_corpus::settle_after;
use gandr_surface_diagnostics::Failures;
use gandr_surface_diagnostics::TypeSpellings;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::CarriedOrigins;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::DeprecatedUse;
use gandr_surface_lowering::ImportDeclaration;
use gandr_surface_lowering::ImportResolution;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::InferredExit;
use gandr_surface_lowering::InferredRun;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Mark;
use gandr_surface_lowering::Onto;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::Sealing;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::Unlayable;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::component::Member;
use crate::evaluate::Focused;
use crate::evaluate::Program;
use crate::exercised::Exercised;
use crate::typed::TypeTable;
use crate::typed::TypedRun;
use crate::typed::wanted_types;
use crate::typed::written_types;

/// How many sources a run has lowered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringCount(usize);

impl From<usize> for LoweringCount
{
    /// The count of `lowerings` lowerings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lowerings: usize) -> Self
    {
        Self(lowerings)
    }
}

impl From<LoweringCount> for usize
{
    /// The number of lowerings `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: LoweringCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for LoweringCount
{
    /// Writes the number of lowerings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

impl LoweringCount
{
    /// Count `other`'s lowerings into these, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum of both counts, saturated at the maximum count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wider walk absorbs each source's count into the
    ///   run's, and its report equals the serial walk's lowering count over
    ///   trees and the corpus; a lost or doubled absorption changes that count.
    ///   Saturation is not reached by these witnesses.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
    #[inline]
    #[spec(captures: [before = self.0], ensures: |_| self.0 == before.saturating_add(other.0))]
    pub(crate) fn absorb(
        &mut self,
        other: Self,
    )
    {
        self.0 = self.0.saturating_add(other.0);
    }
}

/// How many spelling passes a run has made: one per judged unit, each
/// spelling every type the unit's checker refusals compare and its failures
/// name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SpellingCount(usize);

impl From<SpellingCount> for usize
{
    /// The number of spelling passes `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: SpellingCount) -> Self
    {
        count.0
    }
}

impl SpellingCount
{
    /// Count one more spelling pass, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count is one more, saturated at the maximum count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a walk over the identity subject counts one pass per
    ///   component, however many sources share it; a pass per member, or none,
    ///   changes the count. Saturation is not reached by the witness.
    /// - witness: `tests::corpus::the_identity_base_is_spelled_once_for_its_importers_595`
    #[inline]
    #[spec(captures: [before = self.0], ensures: |_| self.0 == before.saturating_add(1))]
    pub(crate) fn tick(&mut self)
    {
        self.0 = self.0.saturating_add(1);
    }
}

/// What one source became.
#[expect(
    clippy::large_enum_variant,
    reason = "one per source, moved once into its step; the settled variant is the common one, \
              and boxing it would add an allocation per source to shrink the rare refused one"
)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Composed<'source>
{
    /// The lowering read the source's declarations, and each was checked and
    /// settled against what it states.
    Settled
    {
        /// One report per declared name, and the module's ledger size.
        report: SettleReport<'source>,
        /// The rows of the fragment's exercised table the settled
        /// declarations carry.
        exercised: Exercised,
        /// The refusals no expectation can state, in admission order: each
        /// declaration the lowering refused at its own form files no half,
        /// so no attribute can be read off it.
        unstatable: Vec<LoweringRefusal<'source>>,
        /// Every core node the lowering minted, mapped back to the syntax
        /// that produced it: the table a checker refusal's node is located
        /// through.
        origins: OriginTable,
        /// The types the checker refusals compare, and the types and binders
        /// their failures name, spelled in each spelling while the arena was
        /// at hand: the table a refusal's types are read from.
        spellings: TypeSpellings,
        /// The failure the checking machine kept for each refused body, by
        /// admission position: the rules it stood inside and the hypotheses
        /// in scope.
        failures: Failures,
        /// Every builtin the source's declarations and binders shadowed, in
        /// the order shadowed: under the warn-and-allow policy the source's
        /// binding wins and each is a warning, not a refusal.
        shadowed: Vec<ShadowedBuiltin>,
        /// Every exit the lowering inferred where a path through a body ends,
        /// in source order: each a finding of the `explicit-exits` lint where
        /// an attribute or the run asks for it.
        inferred: Vec<InferredExit>,
        /// Every run the checker inferred where a computation stands in a
        /// position that reads a value, in source order: each a finding of
        /// the `explicit-runs` lint where an attribute or the run asks for it.
        runs: Vec<InferredRun>,
        /// Every written name resolving to a declaration a `deprecated`
        /// attribute marks, in source order: each a finding of the
        /// `deprecated` lint.
        deprecated: Vec<DeprecatedUse<'source>>,
        /// Every binder a lambda or a bind opens, written in a declaration
        /// the checker accepted, that no variable reads, ascending: each a
        /// hint the editor fades. An unused consumable capability is the
        /// checker's refusal, so every such binder may be dropped.
        unused: Vec<ByteSpan>,
        /// Every path import the source writes that no use written in it
        /// reaches, ascending: each a hint the editor fades. An import brings
        /// in its target's own declarations, so one whose target holds no
        /// declaration or constructor a use names may be dropped.
        unreached: Vec<ByteSpan>,
        /// The kernel artifact of every declaration that crossed into the
        /// kernel, in kernel admission order, each under its structured name,
        /// once the module's admission ran; a composition read before its
        /// admission carries none.
        kernel: Maybe<EncodedArtifact, admitted::Absent>,
        /// The module's declarations focused into the command IL, ready to
        /// run any of them.
        program: Program<'source>,
    },
    /// The lowering refused the source as a whole, before any declaration
    /// existed to carry a verdict: a root that is not a list of declarations.
    Refused(LoweringRefusal<'source>),
}

quenchant_shape::reason_enum! {
    /// Why a settled composition carries no kernel artifact.
    pub mod admitted {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module was judged and settled and its [`Admission`]
            /// has not run yet.
            ///
            /// [`Admission`]: super::Admission
            Pending,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a source is handed no admission beside its composition.
    pub mod kept {
        /// The reason none is handed.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Nobody asked for the admissions to be kept.
            Unasked,
            /// No checker judged the source: it could not be read, or its
            /// component's lowering faulted or refused it whole.
            Unjudged,
        }
    }
}

/// Whether judging a component keeps its admission beside its compositions.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Keeping
{
    /// The compositions alone.
    Composed,
    /// The admission too, as it stood before the kernel was offered anything.
    Admission,
}

/// What [`judge_component`] answers: each source's composition, and
/// the component's admission when it was kept.
type KeptComponent<'source> = (
    Vec<Result<Composed<'source>, ComposeFault<'source>>>,
    Maybe<Admission, kept::Absent>,
);

impl Composed<'_>
{
    /// This composition with `kernel` as its kernel artifact.
    ///
    /// # Specification
    /// - requires: `kernel` is the export of this composition's admission.
    /// - ensures: a settled composition carries `kernel` and is otherwise
    ///   unchanged; a whole refusal, which offered the kernel nothing, is
    ///   returned as it was.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composition of a module, judged and then
    ///   admitted, equals the one-step composition, kernel artifact included;
    ///   dropping or replacing the artifact changes it.
    /// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
    /// - witness: `compose::tests::a_judged_module_renders_before_its_admission`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Composed::Settled { ref kernel, .. } => matches!(kernel, Maybe::Present(_)),
        Composed::Refused(_) => true,
    })]
    pub fn admitted(
        self,
        kernel: EncodedArtifact,
    ) -> Self
    {
        match self {
            Self::Settled {
                report,
                exercised,
                unstatable,
                origins,
                spellings,
                failures,
                shadowed,
                inferred,
                runs,
                deprecated,
                unused,
                unreached,
                program,
                ..
            } => Self::Settled {
                report,
                exercised,
                unstatable,
                origins,
                spellings,
                failures,
                shadowed,
                inferred,
                runs,
                deprecated,
                unused,
                unreached,
                kernel: Maybe::Present(kernel),
                program,
            },
            Self::Refused(refusal) => Self::Refused(refusal),
        }
    }
}

/// A lowered module judged and settled, its kernel admission still to run.
///
/// # Specification
/// - requires: constructed by [`judge`].
/// - ensures: carries the settled composition, its kernel artifact pending, or
///   the settle comparison's fault, beside the module's [`Admission`].
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`judge`] and
///   [`Judged::admit`] carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a judged module's reports equal the composition's before
///   the kernel has been offered anything, and admitting it gives the
///   composition; the corpus at every width composes alike through it.
/// - witness: `compose::tests::a_judged_module_renders_before_its_admission`
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
#[derive(Clone, Debug)]
pub struct Judged<'source>
{
    /// The settled composition, its kernel artifact pending, or the settle
    /// fault.
    settled: Result<Composed<'source>, SettleFault>,
    /// What offering the module to the kernel needs.
    admission: Admission,
}

impl<'source> Judged<'source>
{
    /// The settled composition, its kernel artifact pending, or the settle
    /// comparison's fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn settled(&self) -> &Result<Composed<'source>, SettleFault>
    {
        &self.settled
    }

    /// The settled composition, or its fault, and the admission still to
    /// run, apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn into_parts(self) -> (Result<Composed<'source>, SettleFault>, Admission)
    {
        (self.settled, self.admission)
    }

    /// Run the admission and complete the composition with its kernel
    /// artifact.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the settled composition carrying the admission's kernel
    ///   artifact; a kernel disagreement is reported before a settle fault, so
    ///   either fault is the one [`judge_module`] has always reported.
    /// - fails: [`ComposeFault::Readmission`] when the kernel does not
    ///   re-derive an acceptance; else [`ComposeFault::Settle`] when the settle
    ///   comparison refused the verdicts.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ComposeFault::Readmission`]: the kernel disagreed with the checker.
    /// - [`ComposeFault::Settle`]: the verdicts are not the module's own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`judge_module`], which is this after [`judge`].
    /// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
    /// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(Composed::Settled { ref kernel, .. }) => matches!(kernel, Maybe::Present(_)),
        Ok(Composed::Refused(_)) | Err(ComposeFault::Parse(_) | ComposeFault::Lowering(_)) => false,
        Err(ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => true,
    })]
    pub fn admit(self) -> Result<Composed<'source>, ComposeFault<'source>>
    {
        let kernel = self.admission.admit().map_err(ComposeFault::Readmission)?;
        let composed = self.settled.map_err(ComposeFault::Settle)?;
        Ok(composed.admitted(kernel))
    }
}

/// What offering a judged module to the kernel needs: the arena it was
/// judged over, its verdicts, and the structured names the export writes.
///
/// # Specification
/// - requires: constructed by [`judge`].
/// - ensures: the verdicts were judged over the arena, and the names are the
///   module's structured names by admission position.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`Admission::admit`] carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Admission::admit`].
/// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
#[derive(Clone, Debug)]
pub struct Admission
{
    /// The arena the verdicts were judged over, which the readmission mints
    /// its static reducts into.
    arena: CoreArena,
    /// The checker's verdicts.
    verdicts: ModuleReport,
    /// The structured name of every declared name, by admission position.
    names: BTreeMap<ConstantIndex, StructuredName>,
}

impl Admission
{
    /// The arena the verdicts were judged over, before the admission mints
    /// into it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source's declarations, normalised over its
    ///   admission's arena with the definitions its verdicts record, read as
    ///   their runs do.
    /// - witness: `tests::differential::a_transport_along_an_inline_equivalence_normalises_1677`
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &CoreArena
    {
        &self.arena
    }

    /// The checker's verdicts.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arena`].
    /// - witness: `tests::differential::a_transport_along_an_inline_equivalence_normalises_1677`
    #[inline]
    #[must_use]
    pub const fn verdicts(&self) -> &ModuleReport
    {
        &self.verdicts
    }

    /// Offer every declaration the checker accepted to the kernel, and export
    /// what crossed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel artifact of every declaration that crossed, under
    ///   its structured name, when the readmission found no disagreement.
    /// - fails: the first declaration the kernel did not re-derive, as the
    ///   readmission reports it.
    /// - panics: none.
    ///
    /// # Errors
    /// The readmission of the first declaration the kernel did not re-derive.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition and an owed axiom cross under their
    ///   names while a refused declaration and one naming it do not; a module
    ///   judged over a foreign arena is a disagreement.
    /// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
    /// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body readmits every judged declaration; the capture copies each one's constant once"
        )
    )]
    #[spec(
        captures: [judged = self.verdicts.judged().iter().map(gandr_core_checker::Judged::constant)
            .collect::<alloc::vec::Vec<_>>()],
        ensures: |ref ret| ret.as_ref().err().is_none_or(|fault| judged.contains(&fault.constant())),
    )]
    pub fn admit(self) -> Result<EncodedArtifact, bridge::Readmitted>
    {
        self.admit_resuming(
            bridge::LeadingCount::NONE,
            Maybe::Absent(bridge::crossed::Absent::Unasked),
        )
        .artifact
    }

    /// [`admit`](Self::admit), resuming the readmission of the verdicts' first
    /// `boundary` declarations from `crossed`, an earlier readmission's record
    /// of them, and recording them for a later admission to resume.
    ///
    /// # Specification
    /// - requires: `crossed`, when present, was recorded by the readmission of
    ///   verdicts whose first `boundary` declarations were judged as these were
    ///   — the same content, consulting the same answers — which the caller
    ///   compares, as [`bridge::readmit_resuming`] requires.
    /// - ensures: [`admit`](Self::admit)'s artifact or disagreement; how many
    ///   leading declarations the readmission resumed, of how many judged; and
    ///   the record [`bridge::readmit_resuming`] made of the first `boundary`.
    /// - provides: an editor's admission of a document laid out after its
    ///   import closure, which resumes the closure each revision leaves alone.
    /// - fails: as [`admit`](Self::admit), in the artifact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an admission of a laid-out document resumed from the
    ///   record of another revision's admission exports, byte for byte, what a
    ///   whole admission exports, resuming the closure's declarations alone; a
    ///   revision of the closure itself is not resumed.
    /// - witness: `compose::tests::a_resumed_admission_exports_what_a_whole_one_does_776`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body readmits every judged declaration; the capture copies each one's constant once"
        )
    )]
    #[spec(
        captures: [judged = self.verdicts.judged().iter().map(gandr_core_checker::Judged::constant)
            .collect::<alloc::vec::Vec<_>>()],
        ensures: |ref ret| usize::from(ret.judged) == judged.len() && ret.resumed <= ret.judged
            && ret.artifact.as_ref().err().is_none_or(|fault| judged.contains(&fault.constant())),
    )]
    #[must_use]
    pub fn admit_resuming(
        self,
        boundary: bridge::LeadingCount,
        crossed: Maybe<&bridge::Crossed, bridge::crossed::Absent>,
    ) -> Resumption
    {
        self.admit_retiring(boundary, crossed, &Unretired).whole()
    }

    /// [`admit_resuming`](Self::admit_resuming), polling `retirement` before
    /// each declaration the readmission crosses: retired, it stops there and
    /// answers the record of the declarations it crossed before.
    ///
    /// # Specification
    /// - requires: as [`admit_resuming`](Self::admit_resuming).
    /// - ensures: while every poll answers wanted, [`Polled::Whole`] with
    ///   [`admit_resuming`](Self::admit_resuming)'s answer; retired before a
    ///   declaration, [`Polled::Retired`] with the retirement and the record
    ///   [`bridge::readmit_retiring`] made of the declarations before it, and
    ///   no artifact.
    /// - provides: an editor's admission that a newer revision overtakes stops
    ///   at its next declaration, and the next admission resumes what it
    ///   crossed.
    /// - fails: as [`admit_resuming`](Self::admit_resuming), in the artifact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an admission retired part way, then resumed from its
    ///   record, exports what a whole admission exports.
    /// - witness: `compose::tests::a_retired_admission_resumes_from_its_record_1547`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body readmits every judged declaration; the capture copies each one's constant once"
        )
    )]
    #[spec(
        captures: [judged = self.verdicts.judged().iter().map(gandr_core_checker::Judged::constant)
            .collect::<alloc::vec::Vec<_>>()],
        ensures: |ref ret| match *ret {
            Polled::Whole(ref whole) => usize::from(whole.judged) == judged.len() && whole.resumed <= whole.judged
                && whole.artifact.as_ref().err().is_none_or(|fault| judged.contains(&fault.constant())),
            Polled::Retired(_, Maybe::Present(ref record)) => usize::from(record.boundary()) < judged.len(),
            Polled::Retired(_, Maybe::Absent(_)) => true,
        },
    )]
    pub fn admit_retiring<Poll>(
        mut self,
        boundary: bridge::LeadingCount,
        crossed: Maybe<&bridge::Crossed, bridge::crossed::Absent>,
        retirement: &Poll,
    ) -> Polled<Resumption, Poll::Retired, Maybe<bridge::Crossed, bridge::crossed::Absent>>
    where
        Poll: Retirement,
    {
        let judged = bridge::LeadingCount::from(self.verdicts.judged().len());
        let (readmission, mut recorded) = match readmitted(
            &mut self.arena,
            &self.verdicts,
            (boundary, crossed),
            retirement,
        ) {
            Polled::Whole(whole) => whole,
            Polled::Retired(retired, held) => return Polled::Retired(retired, held),
        };
        Polled::Whole(match readmission {
            Ok(readmission) => Resumption {
                resumed: readmission.resumed(),
                judged,
                artifact: Ok(readmission.export_resuming(self.names, crossed, &mut recorded)),
                crossed: recorded,
            },
            Err(fault) => Resumption {
                artifact: Err(fault),
                resumed: bridge::LeadingCount::NONE,
                judged,
                crossed: recorded,
            },
        })
    }
}

/// What [`Admission::admit_resuming`] answers.
///
/// # Specification
/// - requires: constructed by [`Admission::admit_resuming`].
/// - ensures: no more declarations resumed than judged.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`Admission::admit_resuming`] carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Admission::admit_resuming`].
/// - witness: `compose::tests::a_resumed_admission_exports_what_a_whole_one_does_776`
#[derive(Debug)]
pub struct Resumption
{
    /// The kernel artifact of every declaration that crossed, or the first
    /// declaration the kernel did not re-derive.
    pub artifact: Result<EncodedArtifact, bridge::Readmitted>,
    /// How many leading declarations the readmission resumed rather than
    /// crossed again.
    pub resumed: bridge::LeadingCount,
    /// How many declarations the checker judged.
    pub judged: bridge::LeadingCount,
    /// The record of the first declarations, for a later admission to resume.
    pub crossed: Maybe<bridge::Crossed, bridge::crossed::Absent>,
}

/// Why one source could not be carried through the pipeline: an engine
/// fault, never a verdict about the source.
#[derive(Clone, Debug)]
pub enum ComposeFault<'source>
{
    /// The parser could not commit its tree.
    Parse(MeldError),
    /// The lowering met an engine fault — an exhausted allowance, a tree of
    /// another grammar, a mold outside the grammar's table — so no declaration
    /// of the source can be trusted.
    Lowering(LoweringRefusal<'source>),
    /// The settle comparison was handed verdicts that are not the module's
    /// own.
    Settle(SettleFault),
    /// The kernel did not re-derive a declaration the checker accepted.
    Readmission(bridge::Readmitted),
}

impl fmt::Display for ComposeFault<'_>
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the fault's context and payload; a readmission fault
    ///   includes the declaration's admission position, and a declined
    ///   certificate the kernel's decline, a refused trace led by its class.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter owns the emitted text and exposes
    ///   neither its contents nor a local result carrying the written fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real readmission fault following a mark is rendered
    ///   and its numeric declaration position is independently asserted. This
    ///   detects dropping or replacing that position, not changes to
    ///   explanatory prose or failures of an arbitrary writer.
    /// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Parse(ref fault) => write!(f, "the parser could not commit its tree: {fault}"),
            Self::Lowering(ref refusal) => write!(f, "the lowering faulted: {refusal}"),
            Self::Settle(ref fault) => write!(f, "the settle comparison faulted: {fault}"),
            Self::Readmission(ref readmitted) => {
                write!(
                    f,
                    "the kernel did not re-derive the declaration at position {} the checker accepted: ",
                    usize::from(readmitted.constant())
                )?;
                match *readmitted.outcome() {
                    bridge::Outcome::Rejected(ref error) => {
                        write!(f, "the kernel rejected it: {error}")
                    },
                    bridge::Outcome::Refused(bridge::Refusal::CertificateDeclined {
                        reason,
                        ..
                    }) => write!(
                        f,
                        "the kernel declined the certificate of a step it unfolded: {reason}"
                    ),
                    bridge::Outcome::Refused(refusal) => {
                        write!(f, "the bridge refused to offer it ({})", refusal.classify())
                    },
                    bridge::Outcome::Data { .. }
                    | bridge::Outcome::Defined { .. }
                    | bridge::Outcome::Assumed { .. }
                    | bridge::Outcome::Marked(_)
                    | bridge::Outcome::Suspended
                    | bridge::Outcome::Static => f.write_str("it crossed"),
                }
            },
        }
    }
}

impl core::error::Error for ComposeFault<'_>
{
}

/// The one call into the lowering, counted.
///
/// Nothing else in the crate names the lowering's entry, so the count this
/// module keeps is every source the crate lowers: each source of a unit,
/// once per lowering of the unit.
mod lowering
{
    use alloc::string::String;
    use alloc::sync::Arc;

    use anodized::spec;
    use gandr_core_term::CoreArena;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_lowering::CarriedOrigins;
    use gandr_surface_lowering::ClosureLowering;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Onto;
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::coincide::Decisions;
    use gandr_surface_lowering::lower_unit;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SyntaxTree;

    use super::LoweringCount;
    use super::Unheld;

    /// Lower the sources `unit` lays out in `tree` into `arena` against the
    /// empty outermost scope, each rule block decided through `decisions`,
    /// counting each of them in `lowerings`.
    ///
    /// # Specification
    /// - requires: `tree` was molded under `grammar`.
    /// - ensures: `lowerings` is more by the unit's sources, saturating,
    ///   whatever the lowering answered.
    /// - provides: the lowering's own answer, unchanged.
    /// - fails: the lowering's refusal of the whole module, unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`LoweringRefusal`] the lowering returns for the whole module.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — admitted, wholly refused and declaration-refused
    ///   sources advance the count once; a component of four sources advances
    ///   it by four; the saturation witness separates the penultimate count
    ///   from the maximum. The counter is the declared observation of the
    ///   sources lowered, not a proof of all work inside the lowering.
    /// - witness: `compose::tests::each_composition_lowers_once`
    /// - witness: `script::tests::run_source_counts_lowerings_with_saturation`
    /// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
    #[spec(
        captures: [before = lowerings.0],
        ensures: lowerings.0 == before.saturating_add(unit.sources().len()),
    )]
    pub(super) fn lower<'source>(
        grammar: &Pbg,
        tree: &SyntaxTree<'source>,
        unit: &Unit,
        arena: &mut CoreArena,
        lowerings: &mut LoweringCount,
        decisions: &mut Decisions,
    ) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
    {
        *lowerings = LoweringCount(lowerings.0.saturating_add(unit.sources().len()));
        lower_unit(
            grammar,
            tree,
            unit,
            arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
            decisions,
        )
    }

    /// Lower the closure `text` lays out as `unit` under `grammar`, against
    /// the empty outermost scope, held for the documents laid after it;
    /// each of its sources counted in `lowerings` once its text parses as a
    /// text a document can be laid after.
    ///
    /// # Specification
    /// - requires: `text` lays out `unit`'s sources end to end.
    /// - ensures: on success, `lowerings` is more by the closure's sources,
    ///   saturating; on refusal, unchanged.
    /// - provides: the closure's lowering, once per closure.
    /// - fails: [`Unheld::Parse`] when the text does not parse, and
    ///   [`Unheld::Unlayable`] when its parse repairs it or it ends inside a
    ///   token.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unheld`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure is counted by its own sources, and one that
    ///   ends inside a comment is not held and counts nothing.
    /// - witness: `compose::tests::a_closure_lowers_once_and_resumes_per_document_1033`
    #[spec(
        captures: [before = lowerings.0, sources = unit.sources().len()],
        ensures: |ret| lowerings.0 == if ret.is_ok() { before.saturating_add(sources) } else { before },
    )]
    pub(super) fn suspend(
        grammar: Arc<Pbg>,
        text: String,
        unit: Unit,
        lowerings: &mut LoweringCount,
    ) -> Result<ClosureLowering, Unheld>
    {
        let sources = unit.sources().len();
        let closure = ClosureLowering::new(
            grammar,
            text,
            unit,
            LoweringBudget::DEFAULT,
            Recognition::default(),
            |grammar, text| {
                let parsed = parse(grammar, text).map_err(Unheld::Parse)?;
                parsed.layable().map_err(Unheld::Unlayable)?;
                Ok(parsed.into_tree())
            },
        )?;
        *lowerings = LoweringCount(lowerings.0.saturating_add(sources));
        Ok(closure)
    }

    /// Lower `tree`, a document laid after `closure`'s tree, as `unit` lays
    /// it out, into `arena`, resuming `closure`'s lowering, its rule blocks
    /// decided through `decisions`; each source after the closure's counted
    /// in `lowerings`.
    ///
    /// # Specification
    /// - requires: `tree` lays a document's parse after `closure`'s tree, and
    ///   `unit` lays the closure's sources out first.
    /// - ensures: `lowerings` is more by the unit's sources after the
    ///   closure's, saturating, whatever the lowering answered; the answer is
    ///   [`ClosureLowering::resume`]'s.
    /// - provides: a document's lowering at the cost of its own source.
    /// - fails: the lowering's refusal of the whole module, unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`LoweringRefusal`] the lowering returns for the whole module.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`suspend`].
    /// - witness: `compose::tests::a_closure_lowers_once_and_resumes_per_document_1033`
    #[spec(
        captures: [before = lowerings.0],
        ensures: lowerings.0 == before.saturating_add(
            unit.sources().len().saturating_sub(closure.unit().sources().len())),
    )]
    pub(super) fn resume<'held>(
        closure: &'held ClosureLowering,
        tree: &SyntaxTree<'held>,
        unit: &Unit,
        arena: &mut CoreArena,
        lowerings: &mut LoweringCount,
        decisions: &mut Decisions,
    ) -> Result<LoweredModule<'held>, LoweringRefusal<'held>>
    {
        let after = unit
            .sources()
            .len()
            .saturating_sub(closure.unit().sources().len());
        *lowerings = LoweringCount(lowerings.0.saturating_add(after));
        closure.resume(tree, unit, arena, decisions)
    }

    /// Lower `tree`, a document laid after `closure`'s tree, as `unit` lays
    /// it out, after the nodes of `arena`, resuming `closure`'s lowering on a
    /// copy of `origins`, its rule blocks decided through `decisions`; each
    /// source after the closure's counted in `lowerings` unless the tree is
    /// left to the whole lowering.
    ///
    /// # Specification
    /// - requires: as [`ClosureLowering::resume_onto`].
    /// - ensures: `lowerings` is more by the unit's sources after the
    ///   closure's, saturating, unless the answer is [`Onto::Whole`], which
    ///   lowers nothing; the answer is [`ClosureLowering::resume_onto`]'s.
    /// - provides: a document's lowering after its closure's judged arena.
    /// - fails: the lowering's refusal of the whole module, unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`LoweringRefusal`] the lowering returns for the whole module.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`suspend`].
    /// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
    #[spec(
        captures: [before = lowerings.0],
        ensures: |ret| lowerings.0 == if matches!(ret, Ok(Onto::Whole)) { before } else {
            before.saturating_add(unit.sources().len().saturating_sub(closure.unit().sources().len()))
        },
    )]
    pub(super) fn resume_onto<'held>(
        closure: &'held ClosureLowering,
        tree: &SyntaxTree<'held>,
        unit: &Unit,
        arena: &mut CoreArena,
        origins: &CarriedOrigins,
        lowerings: &mut LoweringCount,
        decisions: &mut Decisions,
    ) -> Result<Onto<'held>, LoweringRefusal<'held>>
    {
        let answer = closure.resume_onto(tree, unit, arena, origins, decisions);
        if !matches!(answer, Ok(Onto::Whole)) {
            let after = unit
                .sources()
                .len()
                .saturating_sub(closure.unit().sources().len());
            *lowerings = LoweringCount(lowerings.0.saturating_add(after));
        }
        answer
    }
}

/// What the lowering made of one parsed source, before any checking.
#[expect(
    clippy::large_enum_variant,
    reason = "one per source, moved once into its judgement; the module is the common variant, \
              and boxing it would add an allocation per source to shrink the rare refused one"
)]
#[derive(Clone, Debug)]
pub enum Lowered<'source>
{
    /// The lowering read the source's declarations, minting their core nodes
    /// in `arena`.
    Module
    {
        /// The lowered module.
        module: LoweredModule<'source>,
        /// The arena its core nodes were minted in.
        arena: CoreArena,
    },
    /// The lowering refused the source as a whole for a reason of the
    /// author's or of the fragment's: a root that is not a list of
    /// declarations.
    Refused(LoweringRefusal<'source>),
}

/// One source parsed and lowered: what the lowering made of it, beside the
/// completion obligations the parser recorded while committing its tree.
#[derive(Clone, Debug)]
pub struct Lowering<'source>
{
    /// The parser's completion obligations, verbatim and in its order.
    obligations: Vec<ObligationInstance>,
    /// What the lowering made of the tree.
    lowered: Lowered<'source>,
}

impl<'source> Lowering<'source>
{
    /// The parser's completion obligations, verbatim and in its order: each
    /// repair the parser made to commit a tree the source did not spell whole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// What the lowering made of the tree, the obligations given up.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_lowered(self) -> Lowered<'source>
    {
        self.lowered
    }

    /// The lowering's refusal of the source as a whole, when it refused it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refused(&self) -> Option<&LoweringRefusal<'source>>
    {
        match self.lowered {
            Lowered::Refused(ref refusal) => Some(refusal),
            Lowered::Module { .. } => None,
        }
    }
}

/// Parse and lower one source: the first half of the composition.
///
/// # Specification
/// - requires: `grammar` is the checked grammar the source is parsed under.
/// - ensures: after parsing succeeds, the source is lowered once into a fresh
///   arena against the empty outermost scope and `lowerings` advances once,
///   saturating. A parse failure leaves the count unchanged. A module the
///   lowering reads is [`Lowered::Module`] with its arena; a whole-source
///   refusal outside the engine-fault class is [`Lowered::Refused`]. Either
///   carries the parser's completion obligations unchanged.
/// - provides: the lowering [`compose()`] judges, for a caller that keeps the
///   lowered module beside the verdicts — the session, which hands the same
///   module to the incremental checker.
/// - fails: [`ComposeFault::Parse`] when the parser cannot commit its tree;
///   [`ComposeFault::Lowering`] for a whole-module refusal of the engine-fault
///   class.
/// - panics: none.
///
/// # Errors
/// - [`ComposeFault::Parse`]: the tree could not be committed.
/// - [`ComposeFault::Lowering`]: the lowering faulted before any declaration
///   could be trusted.
///
/// # Adequacy
/// - hypothesis: L3 — explicit unmolded-token classes and byte spans survive
///   into both an admitted module and a whole-module refusal, while a clean
///   source carries no repair. Exact counts and the saturation boundary detect
///   skipped or repeated lowering. These fixtures do not independently trigger
///   parser commitment failure or a lowering engine fault.
/// - witness: `compose::tests::a_lowering_carries_the_parse_obligations`
/// - witness: `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`
/// - witness: `compose::tests::each_composition_lowers_once`
/// - witness: `script::tests::run_source_counts_lowerings_with_saturation`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: |ref ret| lowerings.0 == if matches!(ret, Err(ComposeFault::Parse(_))) {
        before
    } else {
        before.saturating_add(1)
    } && match *ret {
        Ok(Lowering { lowered: Lowered::Refused(refusal), .. }) =>
            refusal.classify() != FailureClass::EngineFault,
        Ok(Lowering { lowered: Lowered::Module { .. }, .. }) | Err(ComposeFault::Parse(_)) => true,
        Err(ComposeFault::Lowering(refusal)) => refusal.classify() == FailureClass::EngineFault,
        Err(ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => false,
    },
)]
pub fn lower_source<'source>(
    grammar: &Pbg,
    source: SourceText<'source>,
    lowerings: &mut LoweringCount,
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    let parsed = parse(grammar, source).map_err(ComposeFault::Parse)?;
    lower_parsed(
        grammar,
        parsed,
        lowerings,
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
}

/// Lower one source the parser has committed: [`lower_source`] past its
/// parse, each rule block decided through `decisions`.
///
/// # Specification
/// - requires: `grammar` is the checked grammar `parsed` was committed under.
/// - ensures: the tree is lowered once into a fresh arena against the empty
///   outermost scope and `lowerings` advances once, saturating. A module the
///   lowering reads is [`Lowered::Module`] with its arena; a whole-source
///   refusal outside the engine-fault class is [`Lowered::Refused`]. Either
///   carries the parse's completion obligations unchanged.
/// - provides: the lowering of a parse joined from reused form units — the
///   session's — exactly as [`lower_source`] lowers the whole parse.
/// - fails: [`ComposeFault::Lowering`] for a whole-module refusal of the
///   engine-fault class.
/// - panics: none.
///
/// # Errors
/// [`ComposeFault::Lowering`]: the lowering faulted before any declaration
/// could be trusted.
///
/// # Adequacy
/// - hypothesis: L3 — every witness of [`lower_source`] lowers through here,
///   and the session's corpus and edit witnesses lower joined parses through it
///   to the walk's compositions.
/// - witness: `compose::tests::a_lowering_carries_the_parse_obligations`
/// - witness: `compose::tests::each_composition_lowers_once`
#[inline]
#[spec(
    captures: [before = lowerings.0, obligations = parsed.obligations().to_vec()],
    ensures: |ref ret| lowerings.0 == before.saturating_add(1) && match *ret {
        Ok(ref lowering) => lowering.obligations == obligations && match lowering.lowered {
            Lowered::Refused(ref refusal) => refusal.classify() != FailureClass::EngineFault,
            Lowered::Module { .. } => true,
        },
        Err(ComposeFault::Lowering(ref refusal)) => refusal.classify() == FailureClass::EngineFault,
        Err(ComposeFault::Parse(_) | ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => false,
    },
)]
pub fn lower_parsed<'source>(
    grammar: &Pbg,
    parsed: ParseResult<'source>,
    lowerings: &mut LoweringCount,
    decisions: &mut Decisions,
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    lower_parsed_unit(grammar, parsed, &Unit::single(), lowerings, decisions)
}

/// Parse and lower the sources `unit` lays end to end in `source`:
/// [`lower_source`] over a unit of several sources.
///
/// # Specification
/// - requires: `source` is the text `unit` lays out.
/// - ensures: as [`lower_source`], the sources' names resolved within the unit
///   as its imports say, and `lowerings` advancing by each of the unit's
///   sources once the parse succeeds.
/// - provides: the lowering the walk performs for a component (the `component`
///   module).
/// - fails: as [`lower_source`].
/// - panics: none.
///
/// # Errors
/// As [`lower_source`].
///
/// # Adequacy
/// - hypothesis: L3 — a fixture importer lowers over its sibling and settles,
///   the pair counted as two sources lowered.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: |ref ret| lowerings.0 == if matches!(ret, Err(ComposeFault::Parse(_))) {
        before
    } else {
        before.saturating_add(unit.sources().len())
    },
)]
pub fn lower_unit_source<'source>(
    grammar: &Pbg,
    source: SourceText<'source>,
    unit: &Unit,
    lowerings: &mut LoweringCount,
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    let parsed = parse(grammar, source).map_err(ComposeFault::Parse)?;
    lower_parsed_unit(grammar, parsed, unit, lowerings, &mut Decisions::none())
}

/// Lower the sources `unit` lays end to end in the tree `parsed` committed:
/// [`lower_unit_source`] past its parse, each rule block decided through
/// `decisions`.
///
/// # Specification
/// - requires: `grammar` is the checked grammar `parsed` was committed under,
///   over the text `unit` lays out.
/// - ensures: as [`lower_parsed`], over the unit, `lowerings` advancing by each
///   of its sources.
/// - provides: the lowering of a session's document beside the siblings it
///   imports.
/// - fails: as [`lower_parsed`].
/// - panics: none.
///
/// # Errors
/// As [`lower_parsed`].
///
/// # Adequacy
/// - hypothesis: L3 — every witness of [`lower_parsed`] lowers through here; a
///   tree parsed under another grammar is an engine fault.
/// - witness: `compose::tests::each_composition_lowers_once`
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::a_tree_of_another_grammar_faults_every_lowering_route`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: lowerings.0 == before.saturating_add(unit.sources().len()),
)]
pub fn lower_parsed_unit<'source>(
    grammar: &Pbg,
    parsed: ParseResult<'source>,
    unit: &Unit,
    lowerings: &mut LoweringCount,
    decisions: &mut Decisions,
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    let obligations = parsed.obligations().to_vec();
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let lowered = match lowering::lower(grammar, &tree, unit, &mut arena, lowerings, decisions) {
        Ok(module) => Lowered::Module { module, arena },
        Err(refusal) if refusal.classify() == FailureClass::EngineFault => {
            return Err(ComposeFault::Lowering(refusal));
        },
        Err(refusal) => Lowered::Refused(refusal),
    };
    Ok(Lowering {
        obligations,
        lowered,
    })
}

/// Why an import closure's lowering is not held for the documents laid after
/// it: each such document is lowered with its closure, whole.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unheld
{
    /// The closure's text did not parse.
    Parse(MeldError),
    /// The closure's parse cannot stand before a document parsed alone.
    Unlayable(Unlayable),
}

/// The lowering of the import closure `text` lays out as `unit` under
/// `grammar`, held for the documents laid after it: [`lower_resumed_unit`]
/// lowers each such document's own source alone.
///
/// # Specification
/// - requires: `text` lays out `unit`'s sources end to end.
/// - ensures: the closure's sources lowered as [`lower_parsed_unit`] lowers
///   them ahead of any source after them, each counted in `lowerings`.
/// - provides: what a session holds for a document's closure across the
///   document's edits.
/// - fails: [`Unheld`] when the text does not parse, its parse repairs it, or
///   it ends inside a token; nothing is counted.
/// - panics: none.
///
/// # Errors
/// [`Unheld`].
///
/// # Adequacy
/// - hypothesis: L3 — a closure is counted by its own sources, and one that
///   ends inside a comment is not held and counts nothing.
/// - witness: `compose::tests::a_closure_lowers_once_and_resumes_per_document_1033`
#[spec(
    captures: [before = lowerings.0, sources = unit.sources().len()],
    ensures: |ret| lowerings.0 == if ret.is_ok() { before.saturating_add(sources) } else { before }
        && ret.as_ref().map_or(true, |closure| closure.unit().sources().len() == sources),
)]
#[inline]
pub fn lower_closure(
    grammar: Arc<Pbg>,
    text: String,
    unit: Unit,
    lowerings: &mut LoweringCount,
) -> Result<ClosureLowering, Unheld>
{
    lowering::suspend(grammar, text, unit, lowerings)
}

/// [`lower_parsed_unit`] over `parsed`, resuming `closure`'s lowering, each
/// rule block of the document decided through `decisions`.
///
/// `parsed` is a document parsed alone and laid after `closure`'s tree; the
/// closure's sources are not lowered again.
///
/// # Specification
/// - requires: `parsed` is a document's parse laid after `closure`'s tree
///   ([`ParseResult::after`]), and `unit` lays the closure's sources out first.
/// - ensures: as [`lower_parsed_unit`] over `parsed` and `unit`, `lowerings`
///   advancing by the sources after the closure's.
/// - provides: a document's lowering at the cost of its own source.
/// - fails: as [`lower_parsed_unit`].
/// - panics: none.
///
/// # Errors
/// As [`lower_parsed_unit`].
///
/// # Adequacy
/// - hypothesis: L3 — a document resumed twice on one closure lowers each time
///   to the module and arena the whole unit lowers to, counted by its own
///   source; a tree of another grammar is an engine fault, and a document the
///   lowering refuses whole is carried as refused.
/// - witness: `compose::tests::a_closure_lowers_once_and_resumes_per_document_1033`
/// - witness: `compose::tests::a_tree_of_another_grammar_faults_every_lowering_route`
/// - witness: `compose::tests::a_refused_source_is_carried_on_every_resumed_route`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: lowerings.0 == before.saturating_add(
        unit.sources().len().saturating_sub(closure.unit().sources().len())),
)]
pub fn lower_resumed_unit<'held>(
    closure: &'held ClosureLowering,
    parsed: ParseResult<'held>,
    unit: &Unit,
    lowerings: &mut LoweringCount,
    decisions: &mut Decisions,
) -> Result<Lowering<'held>, ComposeFault<'held>>
{
    let obligations = parsed.obligations().to_vec();
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let lowered = match lowering::resume(closure, &tree, unit, &mut arena, lowerings, decisions) {
        Ok(module) => Lowered::Module { module, arena },
        Err(refusal) if refusal.classify() == FailureClass::EngineFault => {
            return Err(ComposeFault::Lowering(refusal));
        },
        Err(refusal) => Lowered::Refused(refusal),
    };
    Ok(Lowering {
        obligations,
        lowered,
    })
}

/// A closure's own declarations judged once, held with the closure's lowering.
///
/// It holds the arena they were judged over, the run and the checker's state
/// after the last of them, the grant, entry and root they were judged and
/// settled under, and their share of the program, the settle comparison and
/// the spellings.
///
/// A document laid after the closure is lowered after this arena's nodes
/// ([`lower_onto_closure`]) and judged on a copy of the rest
/// ([`judge_member_after`]): the closure's declarations are not judged,
/// focused, settled or spelled again, and every revision of the document is
/// judged from the same state, its ids included.
///
/// # Specification
/// - executable: none — a data type; [`judge_member_after`] states what a
///   document judged on it answers.
///
/// # Adequacy
/// - hypothesis: L3 — one judged closure, read by two documents in turn and by
///   a document twice, answers each as a fresh one does.
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[repr(transparent)]
pub struct JudgedClosure(cells::Judged);

/// What judging a closure's own declarations made, its program part and
/// settle reports borrowing the closure's lowering.
#[derive(Debug)]
struct ClosureJudgement<'held>
{
    /// The closure's arena, the checker's nodes minted after the lowering's.
    arena: CoreArena,
    /// The closure's declarations, as the checker reads them.
    declarations: Vec<Declaration>,
    /// The run over them.
    run: ModuleRun,
    /// The checker's state after the last of them.
    checkpoint: Checkpoint,
    /// The grant they were judged under.
    grant: HostGrant,
    /// The entry `grant` names against the closure's worlds.
    entry: HostEntry,
    /// The root they were settled under.
    root: CorpusRoot,
    /// The admission position after the last of them.
    boundary: ConstantIndex,
    /// The nodes their elaborations minted, each beside the node it stands
    /// for, and the binds minted for runs beside their runs.
    elaborated: (Vec<Carried>, Vec<(ValueId, ComputationId)>),
    /// The closure lowering's origin table locating `elaborated`, built the
    /// first time a document is lowered onto `arena`: the table every such
    /// document starts from ([`ClosureLowering::resume_onto`]).
    origins: OnceLock<CarriedOrigins>,
    /// Their share of the program: each focused, before any ran.
    program: Focused<'held>,
    /// Their settle reports, or the settle fault.
    settled: Result<Vec<DeclarationReport<'held>>, SettleFault>,
    /// The types their checker refusals compare and their failures name.
    spellings: TypeSpellings,
}

/// The self-referential cell a judged closure is held in: the closure's
/// lowering with what judging its declarations made.
#[expect(
    clippy::mem_forget,
    reason = "the cells self_cell generates forget their construction guard once the dependent \
              is built: the guard frees the joint allocation only when building unwinds"
)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        recursive_owned_pointer,
        reason = "self_cell names each cell as a marker type parameter of the cell it holds, not \
                  an owning link: the cell owns one joint allocation of the owner and the \
                  dependent, and its drop frees that allocation once without recursing"
    )
)]
mod cells
{
    use alloc::sync::Arc;

    use gandr_surface_lowering::ClosureLowering;
    use self_cell::self_cell;

    use super::ClosureJudgement;

    self_cell!(
        /// The closure's lowering with what judging its declarations made.
        ///
        /// # Specification
        /// trivial.
        pub(super) struct Judged
        {
            owner: Arc<ClosureLowering>,

            #[covariant]
            dependent: ClosureJudgement,
        }
    );
}

impl JudgedClosure
{
    /// `closure`'s own declarations judged under `grant` and settled under
    /// `root`, as [`judge`] judges and settles a module: `None` when the
    /// closure's lowering did not reach its end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the closure's own module ([`ClosureLowering::alone`]) adapted
    ///   and judged with its held capabilities bounded by `grant`, minted into
    ///   the closure's arena, entered at `grant`'s entry read against its
    ///   worlds, its pattern holes kept; the run and the checker's state after
    ///   its last declaration held. Its verdicts, finished on a copy of that
    ///   state, are focused, settled under `root` and spelled as [`judge`]
    ///   does, and each part held.
    /// - provides: what every document laid after the closure is judged from.
    /// - fails: never; a closure with no module is `None`.
    /// - panics: none.
    /// - executable: none — the clauses compare the held parts with a judgement
    ///   of a module no argument carries; the witness judges documents on a
    ///   held and a fresh one and compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
    #[inline]
    #[must_use]
    pub fn new(
        closure: Arc<ClosureLowering>,
        grant: &HostGrant,
        root: CorpusRoot,
    ) -> Option<Self>
    {
        cells::Judged::try_new(closure, |closure| {
            judge_closure(closure, grant, root).ok_or(())
        })
        .ok()
        .map(Self)
    }

    /// The closure's lowering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lowering(&self) -> &ClosureLowering
    {
        self.0.borrow_owner()
    }

    /// The arena the closure's declarations were judged over: what a document
    /// laid after the closure is lowered onto, or an extension of it
    /// ([`lower_onto_closure`]).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arena(&self) -> &CoreArena
    {
        &self.judgement().arena
    }

    /// What judging the closure's declarations made.
    ///
    /// # Specification
    /// trivial.
    fn judgement(&self) -> &ClosureJudgement<'_>
    {
        self.0.borrow_dependent()
    }

    /// The checker's state after the closure's last declaration and the
    /// closure's declarations, when `declarations` lead with them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some` exactly when the closure's declarations are a prefix
    ///   of `declarations`; then the state the checker holds after them and
    ///   that prefix.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document typed after its closure types its own
    ///   declarations alone, on the closure's state.
    /// - witness: `typed::tests::a_document_typed_after_its_closure_types_as_one_typed_whole_776`
    #[spec(ensures: |ret| ret.is_some() == (declarations.get(.. self.judgement().declarations.len())
        == Some(self.judgement().declarations.as_slice())))]
    pub(crate) fn led(
        &self,
        declarations: &[Declaration],
    ) -> Option<(&Checkpoint, &[Declaration])>
    {
        let judgement = self.judgement();
        (declarations.get(.. judgement.declarations.len())
            == Some(judgement.declarations.as_slice()))
        .then_some((&judgement.checkpoint, judgement.declarations.as_slice()))
    }
}

impl fmt::Debug for JudgedClosure
{
    /// The judgement; the lowering is the closure's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_tuple("JudgedClosure")
            .field(self.judgement())
            .finish()
    }
}

/// What [`JudgedClosure::new`] holds of `closure`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`JudgedClosure::new`].
/// - fails: `None` for a closure with no module.
/// - panics: none.
/// - executable: none — as [`JudgedClosure::new`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`JudgedClosure`].
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
fn judge_closure<'held>(
    closure: &'held ClosureLowering,
    grant: &HostGrant,
    root: CorpusRoot,
) -> Option<ClosureJudgement<'held>>
{
    let (mut module, mut arena) = closure.alone()?;
    let declarations = adapt(&module);
    let entry = grant.entry(&declared_worlds(&module));
    let holes = pattern_holes(&module);
    let grants = grant.grants(&mut arena);
    let mut run = ModuleRun::new();
    let checkpoint = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.grant(grants);
        context.enter_at(entry.clone());
        context.keep_pattern_holes(&holes);
        run.judge(&mut context, &declarations, |_, _, _| {});
        context.checkpoint()
    };
    // Every revision of a document laid after the closure copies this arena:
    // frozen, a copy costs the nodes minted after it alone.
    arena.freeze();
    // The closure's verdicts, as a document after it finishes them.
    let mut closing = arena.clone();
    let verdicts = run.clone().finish(&mut CheckingContext::resume(
        &mut closing,
        checkpoint.clone(),
    ));
    let mut program = Program::new(&closing, &module, &verdicts);
    // A run reads the program; the document continues it as focused.
    let focused = program.clone().into_focused();
    let settled = settle(root, &closing, &module, &verdicts, &mut program);
    let first = ConstantIndex::from(0_usize);
    let minted = elaborated(&verdicts, first);
    let spellings = settled.as_ref().map_or_else(
        |_| TypeSpellings::default(),
        |report| {
            module.origins_mut().carry(&minted.0, &minted.1);
            TypeSpellings::of(
                &closing,
                &module,
                report,
                &Failures::of(&verdicts),
                (module.origins(), closure.text()),
            )
        },
    );
    let boundary = module.declarations().last().map_or(first, |last| {
        ConstantIndex::from(usize::from(last.constant()).saturating_add(1))
    });
    Some(ClosureJudgement {
        arena,
        declarations,
        run,
        checkpoint,
        grant: grant.clone(),
        entry,
        root,
        boundary,
        elaborated: minted,
        origins: OnceLock::new(),
        program: focused,
        settled: settled.map(|report| report.declarations().to_vec()),
        spellings,
    })
}

/// How a lowered module is checked: whole, or after a closure judged once.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub enum Checking<'closure>
{
    /// Every declaration of the module is judged.
    Whole,
    /// The module was lowered after the closure's judged arena
    /// ([`lower_onto_closure`]): only its declarations after the closure's are
    /// judged, on a copy of the closure's state.
    After(&'closure JudgedClosure),
}

/// [`lower_resumed_unit`] over `parsed` after `judged`'s closure, minting the
/// document's nodes after `onto`'s, so that the document is judged on a copy
/// of `judged`'s state.
///
/// Each rule block of the document is decided through `decisions`.
///
/// # Specification
/// - requires: as [`lower_resumed_unit`] over [`JudgedClosure::lowering`];
///   `onto` is `judged`'s arena ([`JudgedClosure::arena`]) or a copy that more
///   nodes were minted into after.
/// - ensures: the module [`ClosureLowering::resume_onto`] lowers onto a copy of
///   `onto`, judged [`Checking::After`] `judged`; or, for a tree the closure's
///   lowering does not continue over, [`lower_resumed_unit`]'s answer, judged
///   [`Checking::Whole`]. `lowerings` advances by the sources after the
///   closure's.
/// - provides: a document's lowering whose judgement continues its closure's.
/// - fails: as [`lower_parsed_unit`].
/// - panics: none.
///
/// # Errors
/// As [`lower_parsed_unit`].
///
/// # Adequacy
/// - hypothesis: L3 — a document lowered after a judged closure twice, and
///   another document after it, lowers alike each time and is counted by its
///   own source; a tree of another grammar is an engine fault, and a document
///   the lowering refuses whole is carried as refused.
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
/// - witness: `compose::tests::a_tree_of_another_grammar_faults_every_lowering_route`
/// - witness: `compose::tests::a_refused_source_is_carried_on_every_resumed_route`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: lowerings.0 == before.saturating_add(
        unit.sources().len().saturating_sub(judged.lowering().unit().sources().len())),
)]
pub fn lower_onto_closure<'held>(
    judged: &'held JudgedClosure,
    onto: &CoreArena,
    parsed: ParseResult<'held>,
    unit: &Unit,
    lowerings: &mut LoweringCount,
    decisions: &mut Decisions,
) -> Result<(Lowering<'held>, Checking<'held>), ComposeFault<'held>>
{
    let closure = judged.lowering();
    let obligations = parsed.obligations().to_vec();
    let tree = parsed.into_tree();
    let judgement = judged.judgement();
    let mut arena = onto.clone();
    let origins = judgement.origins.get_or_init(|| {
        let (ref carried, ref binds) = judgement.elaborated;
        closure.carrying(carried, binds)
    });
    let (lowered, checking) = match lowering::resume_onto(
        closure, &tree, unit, &mut arena, origins, lowerings, decisions,
    ) {
        Ok(Onto::Resumed(module)) => (Lowered::Module { module, arena }, Checking::After(judged)),
        Ok(Onto::Whole) => {
            let mut whole = CoreArena::new();
            match lowering::resume(closure, &tree, unit, &mut whole, lowerings, decisions) {
                Ok(module) => (
                    Lowered::Module {
                        module,
                        arena: whole,
                    },
                    Checking::Whole,
                ),
                Err(refusal) if refusal.classify() == FailureClass::EngineFault => {
                    return Err(ComposeFault::Lowering(refusal));
                },
                Err(refusal) => (Lowered::Refused(refusal), Checking::Whole),
            }
        },
        Err(refusal) if refusal.classify() == FailureClass::EngineFault => {
            return Err(ComposeFault::Lowering(refusal));
        },
        Err(refusal) => (Lowered::Refused(refusal), Checking::Whole),
    };
    Ok((
        Lowering {
            obligations,
            lowered,
        },
        checking,
    ))
}

/// Judge and settle one lowered module, its kernel admission left to run.
///
/// # Specification
/// - requires: `module` was lowered from `text` into `arena`; `root` is the
///   corpus root the source sits under.
/// - ensures: the module is adapted to the checker's input, judged with its
///   held capabilities bounded by `grant` minted into `arena` and every
///   declaration entered at `grant`'s entry read against the module's own
///   worlds, built into a [`Program`] and settled under `root`, the program
///   running each declaration that states a run outcome. The settled
///   composition carries one report per declared name, the exercised rows its
///   settled declarations carry, the refusals of the declarations refused at
///   their own form, which no expectation can state, the lowering's origin
///   table, moved rather than copied, the spellings of the types its checker
///   refusals compare and its failures name, each under its binders' names in
///   `text`, the failures themselves, every builtin the source shadowed, every
///   exit the lowering inferred, every run the checker inferred, the program,
///   and no kernel artifact yet ([`admitted::Absent::Pending`]); a settle fault
///   is carried in its place. The admission holds the arena the verdicts were
///   judged over, the verdicts and the module's structured names.
/// - provides: the composition a face renders before the kernel has been
///   offered anything; the readmission mints nothing the settle comparison or
///   the program reads.
/// - fails: never; a settle fault is carried.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a judged module renders the reports its composition
///   renders, before its admission; admitted, it is the composition.
/// - witness: `compose::tests::a_judged_module_renders_before_its_admission`
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `walk::tests::a_grant_bounds_every_source_the_walk_judges`
#[inline]
#[must_use]
#[spec(
    captures: [
        expected_declarations = module.declarations().len(),
        expected_names = module.structured_names(),
    ],
    ensures: |ret| ret.admission.names == expected_names && match ret.settled {
        Ok(Composed::Settled { ref report, ref kernel, .. }) =>
            report.declarations().len() == expected_declarations
                && matches!(kernel, Maybe::Absent(admitted::Absent::Pending)),
        Ok(Composed::Refused(_)) => false,
        Err(_) => true,
    },
)]
pub fn judge<'source>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    grant: &HostGrant,
) -> Judged<'source>
{
    judge_member(
        root,
        (module, text),
        arena,
        grant,
        ByteOffset::from(0_usize),
    )
}

/// Judge and settle one lowered unit, reporting the source that starts at
/// `base`: [`judge`] projected onto the unit's last source.
///
/// # Specification
/// - requires: as [`judge`]; `base` is where the reported source starts in
///   `text`, every source after it in the unit being its own.
/// - ensures: the unit is judged, built and admitted whole, as [`judge`] judges
///   a module; the settled composition reports, of the declarations, refusals,
///   shadowed builtins, inferred exits and inferred runs, those written from
///   `base` on, and of the ledger, the obligations those declarations owe. The
///   origins, failures, program and kernel artifact are the unit's.
/// - provides: a document's composition over the siblings it imports, the
///   session's.
/// - fails: never; a settle fault is carried.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an importer judged over its sibling reports its own
///   declarations alone and settles.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
#[inline]
#[must_use]
#[spec(
    captures: [expected_declarations = module.declarations().len()],
    ensures: |ret| match ret.settled {
        Ok(Composed::Settled { ref report, .. }) =>
            report.declarations().len() <= expected_declarations
                && report.declarations().iter().all(|declaration| declaration.span().start() >= base),
        Ok(Composed::Refused(_)) => false,
        Err(_) => true,
    },
)]
pub fn judge_member<'source>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    grant: &HostGrant,
    base: ByteOffset,
) -> Judged<'source>
{
    judge_member_after(root, (module, text), arena, (grant, Checking::Whole), base)
}

/// [`judge_member`] of a module checked as `checking` says.
///
/// After a closure judged once, its declarations are taken as judged, focused,
/// settled and spelled, and the module's later ones judged on a copy of its
/// state.
///
/// # Specification
/// - requires: as [`judge_member`]; under [`Checking::After`], `module` and
///   `arena` are [`lower_onto_closure`]'s after that closure.
/// - ensures: as [`judge_member`], the verdicts one run over the module's
///   declarations answers when it is judged in two stretches: the closure's, as
///   [`JudgedClosure::new`] judged them, then the rest on a copy of the state
///   after them; the program, settle reports and spellings the closure's share
///   of each continued over the rest. The closure's judgement is taken when
///   `grant` and `root` are the ones it was judged and settled under, the entry
///   `grant` names against the module's worlds is the one it names against the
///   closure's, and the module's leading declarations are the closure's;
///   otherwise, and under [`Checking::Whole`], every declaration is judged over
///   `arena`.
/// - provides: a document's composition at the cost of its own declarations'
///   judgements.
/// - fails: never; a settle fault is carried.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a document judged after a judged closure twice, and
///   another document after it, composes as each does judged after a fresh one,
///   and reports what the whole route reports of its own declarations.
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[inline]
#[must_use]
#[spec(
    captures: [expected_declarations = module.declarations().len()],
    ensures: |ret| match ret.settled {
        Ok(Composed::Settled { ref report, .. }) =>
            report.declarations().len() <= expected_declarations
                && report.declarations().iter().all(|declaration| declaration.span().start() >= base),
        Ok(Composed::Refused(_)) => false,
        Err(_) => true,
    },
)]
pub fn judge_member_after<'source>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    (grant, checking): (&HostGrant, Checking<'source>),
    base: ByteOffset,
) -> Judged<'source>
{
    judge_member_after_retiring(
        root,
        (module, text),
        arena,
        (grant, checking),
        base,
        &Unretired,
    )
    .whole()
}

/// [`judge_member_after`], polling `retirement` before each declaration it
/// judges and once more before the module is tabled, built and settled.
///
/// Under [`Checking::Whole`] it is [`judge_member`] polled.
///
/// # Specification
/// - requires: as [`judge_member_after`].
/// - ensures: [`Polled::Whole`] with what [`judge_member_after`] answers when
///   every poll answered wanted; otherwise [`Polled::Retired`] with what the
///   first poll to answer retired named, nothing of the judgement kept.
/// - fails: never; a settle fault is carried.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a judgement retired before its second declaration, or
///   after its last, answers retired; one never retired reads its poll once
///   before each declaration and once before the settle, and answers what
///   [`judge_member_after`] answers.
/// - witness: `compose::tests::a_retired_member_judgement_keeps_nothing_1663`
#[inline]
#[must_use]
#[spec(
    captures: [expected_declarations = module.declarations().len()],
    ensures: |ref ret| if let Polled::Whole(ref judged) = *ret {
        match judged.settled {
            Ok(Composed::Settled { ref report, .. }) =>
                report.declarations().len() <= expected_declarations
                    && report.declarations().iter().all(|declaration| declaration.span().start() >= base),
            Ok(Composed::Refused(_)) => false,
            Err(_) => true,
        }
    } else {
        true
    },
)]
pub fn judge_member_after_retiring<'source, Poll>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    (grant, checking): (&HostGrant, Checking<'source>),
    base: ByteOffset,
    retirement: &Poll,
) -> Polled<Judged<'source>, Poll::Retired, ()>
where
    Poll: Retirement,
{
    let last = Member {
        start: base,
        end: ByteOffset::from(text.as_ref().len()),
    };
    match judge_members(
        root,
        (module, text),
        arena,
        (grant, checking),
        (&[], last),
        (&mut SpellingCount::default(), Tabling::Untabled),
        retirement,
    ) {
        Polled::Whole((projected, admission, _untabled)) => Polled::Whole(Judged {
            settled: projected.last,
            admission,
        }),
        Polled::Retired(retired, ()) => Polled::Retired(retired, ()),
    }
}

/// [`judge_member_after`], keeping the type table of the module's own
/// source — the source of `unit` starting at `base` — from the judgement's
/// own run.
///
/// # Specification
/// - requires: as [`judge_member_after`]; `module` lowers `text` over `unit`.
/// - ensures: the judgement [`judge_member_after`] makes, each declaration
///   judged decided as [`type_module`](gandr_core_checker::type_module) decides
///   it; and the table of the source at `base`, answering each position as
///   [`TypeTable::of_parsed_after`] or [`TypeTable::of_parsed_unit`] answers it
///   over the same lowering.
/// - provides: a document's type table at the cost of typing its bodies as
///   written, beside the judgement that checks them.
/// - fails: never; a settle fault is carried, and the table still made.
/// - panics: none.
/// - executable: none — the table's agreement with one typed alone is a claim
///   about a second typing the call never makes; the witness makes it over the
///   corpus.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source judged with its table answers each
///   position as its table typed alone does, and settles as it settles without
///   one.
/// - witness: `tests::corpus::a_judgement_s_table_answers_as_the_table_typed_alone_1521`
#[inline]
pub fn judge_member_tabled<'source>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    (grant, checking): (&HostGrant, Checking<'source>),
    (unit, base): (&Unit, ByteOffset),
) -> (Judged<'source>, Maybe<TypeTable, tabled::Absent>)
{
    judge_member_tabled_retiring(
        root,
        (module, text),
        arena,
        (grant, checking),
        (unit, base),
        &Unretired,
    )
    .whole()
}

/// [`judge_member_tabled`], polling `retirement` as
/// [`judge_member_after_retiring`] polls it.
///
/// # Specification
/// - requires: as [`judge_member_tabled`].
/// - ensures: [`Polled::Whole`] with what [`judge_member_tabled`] answers when
///   every poll answered wanted; otherwise [`Polled::Retired`] with what the
///   first poll to answer retired named, nothing of the judgement or its table
///   kept.
/// - fails: never; a settle fault is carried, and the table still made.
/// - panics: none.
/// - executable: none — as [`judge_member_tabled`].
///
/// # Adequacy
/// - hypothesis: L3 — a tabled judgement retired before its second declaration
///   answers retired; one never retired reads its poll as the untabled one
///   does, and answers what [`judge_member_tabled`] answers.
/// - witness: `compose::tests::a_retired_member_judgement_keeps_nothing_1663`
#[inline]
pub fn judge_member_tabled_retiring<'source, Poll>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    (grant, checking): (&HostGrant, Checking<'source>),
    (unit, base): (&Unit, ByteOffset),
    retirement: &Poll,
) -> Polled<(Judged<'source>, Maybe<TypeTable, tabled::Absent>), Poll::Retired, ()>
where
    Poll: Retirement,
{
    let last = Member {
        start: base,
        end: ByteOffset::from(text.as_ref().len()),
    };
    match judge_members(
        root,
        (module, text),
        arena,
        (grant, checking),
        (&[], last),
        (&mut SpellingCount::default(), Tabling::Tabled(unit)),
        retirement,
    ) {
        Polled::Whole((projected, admission, table)) => Polled::Whole((
            Judged {
                settled: projected.last,
                admission,
            },
            table,
        )),
        Polled::Retired(retired, ()) => Polled::Retired(retired, ()),
    }
}

/// Whether a judgement keeps the type table of the source it judges last.
#[derive(Clone, Copy, Debug)]
enum Tabling<'unit>
{
    /// The judgement keeps no table.
    Untabled,
    /// The judgement keeps the table of the last source of the unit.
    Tabled(&'unit Unit),
}

/// Why a judgement holds no type table.
pub mod tabled
{
    /// The reason a judgement holds no type table.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent
    {
        /// The judgement was not asked to keep one.
        Untabled,
        /// The lowering refused the source whole, so nothing was typed.
        RefusedWhole,
        /// The holder handed its table on.
        Taken,
    }
}

/// What judging a unit came to at each of its sources: each one's settled
/// composition, its kernel artifact pending, or the settle fault.
#[derive(Debug)]
struct Projected<'source>
{
    /// Every source but the last, in the unit's order.
    earlier: Vec<Result<Composed<'source>, SettleFault>>,
    /// The unit's last source.
    last: Result<Composed<'source>, SettleFault>,
}

/// One source's share of a judged unit: what it reports of its own, before
/// the unit-wide tables join it.
#[derive(Debug)]
struct Share<'source>
{
    /// The source's own declarations' reports and the obligations they owe.
    report: SettleReport<'source>,
    /// The exercised rows its settled declarations carry.
    exercised: Exercised,
    /// Its declarations refused at their own form.
    unstatable: Vec<LoweringRefusal<'source>>,
    /// The types the unit's checker refusals compare and its failures name.
    spellings: TypeSpellings,
    /// The builtins it shadowed.
    shadowed: Vec<ShadowedBuiltin>,
    /// The exits the lowering inferred in it.
    inferred: Vec<InferredExit>,
    /// The runs the checker inferred in it.
    runs: Vec<InferredRun>,
    /// The uses of deprecated declarations written in it.
    deprecated: Vec<DeprecatedUse<'source>>,
    /// The binders its accepted declarations write and never read.
    unused: Vec<ByteSpan>,
    /// The path imports it writes that no use of its own reaches.
    unreached: Vec<ByteSpan>,
}

/// What judging a unit whole holds: its composition projected onto its
/// sources, its admission and the type table the judgement kept.
type JudgedUnit<'source> = (
    Projected<'source>,
    Admission,
    Maybe<TypeTable, tabled::Absent>,
);

/// Judge and settle one lowered unit once, and project the composition onto
/// each of its sources `members`.
///
/// # Specification
/// - requires: as [`judge`]; `earlier` then `last` are the unit's sources' own
///   bytes in `text`, in the unit's order.
/// - ensures: the unit is judged, built and settled once, as [`judge`] judges a
///   module. Each source's settled composition reports, of the declarations,
///   refusals, shadowed builtins, inferred exits and inferred runs, those
///   written in its own bytes — a refusal with no span in every source's — and
///   of the ledger, the obligations its declarations owe; the spellings,
///   origins, failures and program are the unit's, shared. A source that is the
///   whole unit reports everything, nothing copied. A settle fault is every
///   source's. The admission holds the arena, the verdicts and the unit's
///   structured names. `spelled` advances once when the unit settles: its one
///   spelling pass. The checker holds every hole the unit's patterns were
///   written with, so a match whose tree leaves an arm to one is refused. Under
///   [`Tabling::Tabled`], each declaration judged is decided as
///   [`type_module`](gandr_core_checker::type_module) decides it, keeping the
///   first formation of every type the last source writes, and the table of the
///   last source is assembled from that run over copies of the module and the
///   arena as the run left them; otherwise no table is. `retirement` is polled
///   before each declaration judged and once more before the unit is tabled,
///   built and settled; a poll that answers retired stops the judgement there,
///   [`Polled::Retired`] with what it named and nothing kept.
/// - fails: never; a settle fault is carried.
/// - panics: none.
/// - intension: one check, one program, one settle comparison and one spelling
///   pass per unit; the unit-wide tables are copied once for each source but
///   the last, which takes them.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond judged as one component reports each source's
///   own declarations at each source, and a unit of one source reports all of
///   its own; a subject whose importers share their base's component is spelled
///   once per component; a match leaving an arm to a pattern hole, beside one
///   whose arm body is a hole, separates the pattern hole from the term hole. A
///   closure judged under another grant or entry is not continued: the document
///   is judged whole and reports its own declarations alone, and each source of
///   a component reports its own share.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `tests::corpus::the_identity_base_is_spelled_once_for_its_importers_595`
/// - witness: `tests::corpus::the_fixture_root_settles_every_fixture`
/// - witness: `compose::tests::a_closure_judged_otherwise_is_not_continued`
/// - witness: `compose::tests::each_source_of_a_component_reports_its_own_share`
/// - witness: `compose::tests::a_retired_member_judgement_keeps_nothing_1663`
#[spec(ensures: |ref ret| if let Polled::Whole(ref whole) = *ret {
    whole.0.earlier.len() == earlier.len()
} else {
    true
})]
fn judge_members<'source, Poll>(
    root: CorpusRoot,
    (mut module, text): (LoweredModule<'source>, SourceText<'source>),
    mut arena: CoreArena,
    (grant, checking): (&HostGrant, Checking<'source>),
    (earlier, last): (&[Member], Member),
    (spelled, tabling): (&mut SpellingCount, Tabling<'_>),
    retirement: &Poll,
) -> Polled<JudgedUnit<'source>, Poll::Retired, ()>
where
    Poll: Retirement,
{
    let declarations = adapt(&module);
    let entry = grant.entry(&declared_worlds(&module));
    let holes = pattern_holes(&module);
    let after = match checking {
        Checking::After(closure) => Some(closure.judgement()).filter(|judgement| {
            judgement.grant == *grant
                && judgement.root == root
                && judgement.entry == entry
                && declarations.get(.. judgement.declarations.len())
                    == Some(judgement.declarations.as_slice())
        }),
        Checking::Whole => None,
    };
    let written = match tabling {
        Tabling::Tabled(_) => Some(written_types(&module, &arena, last.start)),
        Tabling::Untabled => None,
    };
    let (verdicts, read) = {
        let (mut context, mut run, judged) = if let Some(closure) = after {
            let context = CheckingContext::resume(&mut arena, closure.checkpoint.clone());
            let judged = declarations
                .get(closure.declarations.len() ..)
                .unwrap_or_default();
            (context, closure.run.clone(), judged)
        }
        else {
            let grants = grant.grants(&mut arena);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.grant(grants);
            context.enter_at(entry);
            (context, ModuleRun::new(), declarations.as_slice())
        };
        context.keep_pattern_holes(&holes);
        if let Some(ref written) = written {
            run.keep_typings();
            context.keep_formations(Formations::Firsts(wanted_types(written)));
        }
        if let Polled::Retired(retired, ()) =
            run.judge_retiring(&mut context, judged, |_, _, _| {}, retirement)
        {
            return Polled::Retired(retired, ());
        }
        let read = run
            .take_typings()
            .zip(written)
            .map(|(typed, written)| TypedRun::read(&context, typed, written));
        (run.finish(&mut context), read)
    };
    if let Demand::Retired(retired) = retirement.demand() {
        return Polled::Retired(retired, ());
    }
    let table = match (tabling, read) {
        (Tabling::Tabled(unit), Some(read)) => Maybe::Present(TypeTable::assemble(
            text,
            (module.clone(), arena.clone()),
            read,
            (unit, last.start),
        )),
        (Tabling::Tabled(_), None) | (Tabling::Untabled, _) => {
            Maybe::Absent(tabled::Absent::Untabled)
        },
    };
    let names = module.structured_names();
    let mut program = after.map_or_else(
        || Program::new(&arena, &module, &verdicts),
        |closure| Program::after(closure.program.clone(), &arena, &module, &verdicts),
    );
    let settled_report = match after {
        Some(closure) => closure
            .settled
            .as_ref()
            .map_err(|&fault| fault)
            .and_then(|earlier| {
                settle_after(root, &arena, &module, &verdicts, &mut program, earlier)
            }),
        None => settle(root, &arena, &module, &verdicts, &mut program),
    };
    let projected = match settled_report {
        Ok(report) => {
            let failures = Failures::of(&verdicts);
            located(
                module.origins_mut(),
                &verdicts,
                after.map_or_else(|| ConstantIndex::from(0_usize), |closure| closure.boundary),
            );
            let spellings = after.map_or_else(
                || {
                    TypeSpellings::of(
                        &arena,
                        &module,
                        &report,
                        &failures,
                        (module.origins(), text),
                    )
                },
                |closure| {
                    TypeSpellings::after(
                        &closure.spellings,
                        closure.boundary,
                        (&arena, &module),
                        (&report, &failures),
                        (module.origins(), text),
                    )
                },
            );
            spelled.tick();
            let unit = Unitwide {
                unstatable: unstatable(&module),
                runs: inferred_runs(&module, &verdicts),
                deprecated: module.deprecated_uses(&arena),
            };
            let whole = earlier.is_empty() && usize::from(last.start) == 0_usize;
            let earlier = earlier
                .iter()
                .map(|&member| {
                    let own = owned(&report, (&module, &verdicts), member);
                    let held = share(member, (own, spellings.clone()), (&arena, &module), &unit);
                    Ok(settled(
                        held,
                        (module.origins().clone(), failures.clone(), program.clone()),
                    ))
                })
                .collect();
            let own = if whole {
                report
            }
            else {
                owned(&report, (&module, &verdicts), last)
            };
            let last_share = share(last, (own, spellings), (&arena, &module), &unit);
            Projected {
                earlier,
                last: Ok(settled(
                    last_share,
                    (module.into_origins(), failures, program),
                )),
            }
        },
        Err(fault) => Projected {
            earlier: earlier.iter().map(|_| Err(fault)).collect(),
            last: Err(fault),
        },
    };
    Polled::Whole((
        projected,
        Admission {
            arena,
            verdicts,
            names,
        },
        table,
    ))
}

/// What a judged unit holds once for all of its sources, read by [`share`].
#[derive(Debug)]
struct Unitwide<'source>
{
    /// The unit's declarations refused at their own form.
    unstatable: Vec<LoweringRefusal<'source>>,
    /// The runs the checker inferred over the unit.
    runs: Vec<InferredRun>,
    /// The uses of deprecated declarations over the unit, ascending.
    deprecated: Vec<DeprecatedUse<'source>>,
}

/// The report of the declarations written in `member`, owing what their
/// verdicts owe.
///
/// # Specification
/// - requires: `report` settled `verdicts`, judged over `module`'s
///   declarations.
/// - ensures: [`SettleReport::within`] `member`, its ledger the number of
///   `verdicts`' obligations owed by a constant from the member's first
///   declaration up to the first declaration after it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an importer reports its own declarations, its sibling's
///   obligations left to the sibling; each source of a component, separated by
///   one line, reports exactly the declarations written in it.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::each_source_of_a_component_reports_its_own_share`
#[spec(ensures: |ref ret| ret.declarations().iter().all(|declaration| member.start <= declaration.span().start() && declaration.span().start() <= member.end))]
fn owned<'source>(
    report: &SettleReport<'source>,
    (module, verdicts): (&LoweredModule<'source>, &ModuleReport),
    member: Member,
) -> SettleReport<'source>
{
    let written = |span: ByteSpan| member.start <= span.start() && span.start() <= member.end;
    let constant = |found: Option<&LoweredDeclaration<'_>>| {
        found.map_or_else(
            || ConstantIndex::from(usize::MAX),
            LoweredDeclaration::constant,
        )
    };
    let first = constant(
        module
            .declarations()
            .iter()
            .find(|declaration| written(declaration.span())),
    );
    let after = constant(
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.span().start() > member.end),
    );
    let owed = verdicts
        .ledger()
        .entries()
        .iter()
        .filter(|entry| (first .. after).contains(&entry.absence().constant()))
        .count();
    report.within(member.start, member.end, ObligationCount::from(owed))
}

/// The share of a judged unit the source `member` reports, its report
/// `report` already its own and `spellings` the unit's.
///
/// # Specification
/// - requires: `report` is [`owned`] of `member`, or the whole unit's for a
///   source that is the whole unit; `spellings` and `unit` are the unit's.
/// - ensures: `report`, the exercised rows it carries, `spellings`, and of the
///   unit's refusals at a declaration's own form, shadowed builtins, inferred
///   exits, inferred runs and deprecated uses, those written in `member` —
///   starting within its own bytes, its end included — a refusal with no span
///   kept.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`judge_members`].
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
/// - witness: `compose::tests::each_source_of_a_component_reports_its_own_share`
#[spec(ensures: |ref ret| ret.shadowed.iter().all(|shadow| member.start <= shadow.span.start() && shadow.span.start() <= member.end)
    && ret.runs.iter().all(|run| member.start <= run.span.start() && run.span.start() <= member.end)
    && ret.deprecated.iter().all(|used| member.start <= used.span.start() && used.span.start() <= member.end)
    && ret.unused.iter().all(|span| member.start <= span.start() && span.start() <= member.end)
    && ret.unreached.iter().all(|span| member.start <= span.start() && span.start() <= member.end))]
fn share<'source>(
    member: Member,
    (report, spellings): (SettleReport<'source>, TypeSpellings),
    (arena, module): (&CoreArena, &LoweredModule<'source>),
    unit: &Unitwide<'source>,
) -> Share<'source>
{
    let own = |span: ByteSpan| member.start <= span.start() && span.start() <= member.end;
    let exercised = Exercised::of(arena, module, &report);
    let mut unstatable = unit.unstatable.clone();
    unstatable.retain(|refusal| match refusal.span() {
        Maybe::Present(span) => own(span),
        Maybe::Absent(_) => true,
    });
    let mut shadowed = module.recognition().shadowed().to_vec();
    shadowed.retain(|shadow| own(shadow.span));
    let mut inferred = module.inferred_exits().to_vec();
    inferred.retain(|exit| own(exit.span));
    let mut runs = unit.runs.clone();
    runs.retain(|run| own(run.span));
    let deprecated = unit
        .deprecated
        .iter()
        .filter(|used| own(used.span))
        .cloned()
        .collect();
    let unused = unused_binders(arena, module, &report, own);
    let unreached = unreached_imports(module, member);
    Share {
        report,
        exercised,
        unstatable,
        spellings,
        shadowed,
        inferred,
        runs,
        deprecated,
        unused,
        unreached,
    }
}

/// The binders a lambda or a bind of `arena` opens in the declarations
/// `report` judged, written where `own` holds, that no use of `module` reads,
/// ascending and once each.
///
/// Every other opener — a capability scope, a placement, a split — binds into
/// the linear zone, and a name one of those records is not answered for a
/// lambda or a bind recording it too. A lambda or a bind binds into the
/// intuitionistic zone, which drops a binder freely, so its binders may all be
/// dropped whatever the judgement made of their declaration: accepted, owed,
/// suspended or refused. The one binder such an opener could hold that may
/// not be dropped is a consumable capability, which never forms: the checker
/// refuses its type as [`CheckRefusal::CapabilityConsumable`], and a
/// declaration so refused answers nothing. Nor does one the lowering refused
/// or the corpus guarded. Both halves of an answered declaration are read. A
/// use is a written variable, or a name the lowering resolved to the binder: a
/// type naming it among them.
///
/// # Specification
/// - ensures: every span returned is a written binder of `module`'s origins
///   whose every opener is a lambda or a bind, `own` holds of it, no written
///   variable and no binder resolution reads it, and it lies within a half of a
///   declaration `report` reports as judged, other than refused as
///   [`CheckRefusal::CapabilityConsumable`]; the spans ascend without repeats.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — parameters, `run` binders, pattern variables and lambda
///   binders used and unused, a binder read only in a type, a constructor's
///   telescope, a handled capability, a placement's binders, refused
///   declarations' binders before and after their refusal, and a consumable
///   capability's declaration.
/// - witness: `compose::tests::each_binder_no_variable_reads_is_unused`
#[spec(ensures: |ref ret| ret.windows(2).all(|pair| matches!(*pair, [first, second] if first < second)))]
fn unused_binders(
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    report: &SettleReport<'_>,
    own: impl Fn(ByteSpan) -> bool,
) -> Vec<ByteSpan>
{
    let answered: BTreeSet<ConstantIndex> = report
        .declarations()
        .iter()
        .filter(|declaration| match declaration.produced() {
            Produced::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Suspended(_),
            ) => true,
            Produced::Judged(Verdict::Refused(refusal)) => {
                !matches!(refusal, CheckRefusal::CapabilityConsumable(_))
            },
            Produced::Unlowered(_) | Produced::Guarded(_) => false,
        })
        .map(DeclarationReport::constant)
        .collect();
    let extents: Vec<ByteSpan> = module
        .declarations()
        .iter()
        .filter(|declaration| answered.contains(&declaration.constant()))
        .flat_map(|declaration| {
            let halves = declaration.halves();
            [halves.signature, halves.definition]
        })
        .filter_map(|half| match half {
            Maybe::Present(at) => Some(at.span),
            Maybe::Absent(_) => None,
        })
        .collect();
    let origins = module.origins();
    let opens = |opener: ComputationId| {
        matches!(
            arena.computation(opener),
            Some(&(Computation::Lambda(_) | Computation::Bind(..)))
        )
    };
    let held: BTreeSet<ByteSpan> = origins
        .binders()
        .iter()
        .filter(|binder| !opens(binder.0))
        .map(|binder| binder.1.span())
        .collect();
    let written = |variable: ValueId| matches!(origins.value(variable), Maybe::Present(origin) if origin.provenance() == Provenance::Written);
    let read: BTreeSet<ByteSpan> = origins
        .bindings()
        .iter()
        .filter(|binding| written(binding.0))
        .map(|binding| binding.1)
        .chain(
            module
                .resolutions()
                .iter()
                .filter_map(|resolution| match resolution.1 {
                    Resolution::Binder(binder) => Some(binder),
                    Resolution::Declaration(_) | Resolution::Constructor { .. } => None,
                }),
        )
        .collect();
    let mut unused: Vec<ByteSpan> = origins
        .binders()
        .iter()
        .filter(|binder| opens(binder.0) && binder.1.provenance() == Provenance::Written)
        .map(|binder| binder.1.span())
        .filter(|&span| {
            own(span)
                && !read.contains(&span)
                && !held.contains(&span)
                && extents
                    .iter()
                    .any(|extent| extent.start() <= span.start() && span.end() <= extent.end())
        })
        .collect();
    unused.sort_unstable();
    unused.dedup();
    unused
}

/// The bytes of each path import written in `member` that no name lookup was
/// answered through, ascending and once each.
///
/// A name after a refusal in its declaration is never looked up, so a source
/// holding a declaration the lowering refused answers none.
///
/// # Specification
/// - requires: `member` is a source's own bytes in the unit `module` lowered.
/// - ensures: every span returned is the bytes of an import of `module`
///   starting in `member` whose address resolved to a source of the unit and
///   that [`LoweredModule::reached_imports`] does not hold; none when a
///   declaration starting in `member` was refused; the spans ascend without
///   repeats.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an importer reading a sibling's value, its constructor,
///   its family only in a type, a module member, through an alias, and nothing;
///   an unresolved import; a refused declaration.
/// - witness: `compose::tests::an_import_no_lookup_reaches_is_unreached`
#[spec(ensures: |ref ret| ret.windows(2).all(|pair| matches!(*pair, [first, second] if first < second)))]
fn unreached_imports(
    module: &LoweredModule<'_>,
    member: Member,
) -> Vec<ByteSpan>
{
    let own = |offset: ByteOffset| member.start <= offset && offset <= member.end;
    let refused = module.declarations().iter().any(|declaration| {
        own(declaration.span().start())
            && matches!(declaration.outcome(), DeclarationOutcome::Refused(_))
    });
    if refused {
        return Vec::new();
    }
    let reached = module.reached_imports();
    let mut unreached: Vec<ByteSpan> = module
        .imports()
        .iter()
        .filter(|import| own(import.span().start()))
        .filter(|import| {
            matches!(
                import.resolution(),
                ImportResolution::Path(ImportTarget::Source(_))
            )
        })
        .map(ImportDeclaration::span)
        .filter(|span| reached.binary_search(span).is_err())
        .collect();
    unreached.sort_unstable();
    unreached.dedup();
    unreached
}

/// The settled composition of one source's `share`, joined by the unit-wide
/// origins, failures and program, its kernel artifact pending.
///
/// # Specification
/// trivial.
fn settled<'source>(
    share: Share<'source>,
    (origins, failures, program): (OriginTable, Failures, Program<'source>),
) -> Composed<'source>
{
    Composed::Settled {
        report: share.report,
        exercised: share.exercised,
        unstatable: share.unstatable,
        origins,
        spellings: share.spellings,
        failures,
        shadowed: share.shadowed,
        inferred: share.inferred,
        unused: share.unused,
        unreached: share.unreached,
        runs: share.runs,
        deprecated: share.deprecated,
        kernel: Maybe::Absent(admitted::Absent::Pending),
        program,
    }
}

/// Judge what the lowering made of one component once, and project the
/// composition onto each of its sources, keeping the component's admission
/// beside them when `keeping` asks for it.
///
/// # Specification
/// - requires: the lowering read `text`, the component's, whose sources' own
///   bytes are `members` in the unit's order; `root` is the corpus root they
///   sit under.
/// - ensures: one composition per source of `members`, in order. A module the
///   lowering read is judged, settled and admitted once and projected as
///   [`judge_members`] projects it, each source's composition carrying the
///   component's kernel artifact; a component of one source is
///   [`judge_lowering`] at offset zero. A whole-component refusal is every
///   source's. `spelled` advances once for a module the lowering read and
///   settled, however many sources it has. Beside the compositions, under
///   [`Keeping::Admission`], the admission of a module the lowering read as it
///   stood before the kernel was offered anything — its arena, verdicts and
///   names — or [`kept::Absent::Unjudged`] for a component the lowering refused
///   whole or that has no source; under [`Keeping::Composed`],
///   [`kept::Absent::Unasked`] and no copy made.
/// - provides: the walk's verdict at each source of a component, the component
///   lowered, checked and spelled once, and a hold on its checked core for a
///   differential that evaluates it apart from the program.
/// - fails: per source, as [`judge_module`]: a kernel disagreement is every
///   source's [`ComposeFault::Readmission`], since the component's environment
///   could not be built past it; otherwise a settle fault is every source's
///   [`ComposeFault::Settle`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond judged whole reports each source's own
///   declarations, each certificate holding the base's segments once, first;
///   the corpus at every width composes alike; a corpus walk that keeps the
///   admissions evaluates every `runs` item of the corpus from them.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
/// - witness: `tests::corpus::the_identity_base_is_spelled_once_for_its_importers_595`
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
#[spec(ensures: |ref ret| ret.0.len() == members.len() && match ret.1 {
    Maybe::Present(_) | Maybe::Absent(kept::Absent::Unjudged) => keeping == Keeping::Admission,
    Maybe::Absent(kept::Absent::Unasked) => keeping == Keeping::Composed,
})]
pub fn judge_component<'source>(
    root: CorpusRoot,
    (lowering, text): (Lowering<'source>, SourceText<'source>),
    grant: &HostGrant,
    (members, spelled): (&[Member], &mut SpellingCount),
    keeping: Keeping,
) -> KeptComponent<'source>
{
    let unkept = match keeping {
        Keeping::Composed => kept::Absent::Unasked,
        Keeping::Admission => kept::Absent::Unjudged,
    };
    let Some((&last, earlier)) = members.split_last()
    else {
        return (Vec::new(), Maybe::Absent(unkept));
    };
    match lowering.into_lowered() {
        Lowered::Module { module, arena } => {
            let (projected, admission, _untabled) = judge_members(
                root,
                (module, text),
                arena,
                (grant, Checking::Whole),
                (earlier, last),
                (spelled, Tabling::Untabled),
                &Unretired,
            )
            .whole();
            let kept = match keeping {
                Keeping::Composed => Maybe::Absent(kept::Absent::Unasked),
                Keeping::Admission => Maybe::Present(admission.clone()),
            };
            let composed = match admission.admit() {
                Ok(kernel) => {
                    let mut composed: Vec<_> = projected
                        .earlier
                        .into_iter()
                        .map(|held| {
                            held.map(|composed| composed.admitted(kernel.clone()))
                                .map_err(ComposeFault::Settle)
                        })
                        .collect();
                    composed.push(
                        projected
                            .last
                            .map(|composed| composed.admitted(kernel))
                            .map_err(ComposeFault::Settle),
                    );
                    composed
                },
                Err(fault) => members
                    .iter()
                    .map(|_| Err(ComposeFault::Readmission(fault.clone())))
                    .collect(),
            };
            (composed, kept)
        },
        Lowered::Refused(refusal) => (
            members
                .iter()
                .map(|_| Ok(Composed::Refused(refusal)))
                .collect(),
            Maybe::Absent(unkept),
        ),
    }
}

/// The runs the checker inferred over `module`, joined with the lowering's
/// record of where each nested computation stands.
///
/// # Specification
/// - requires: `verdicts` are the checker's over `module`'s declarations.
/// - ensures: one record per nested computation the checker decided to run in
///   any elaborated body — bound before its region, or standing as what it
///   returns, which runs purely — as [`LoweredModule::inferred_runs`] lists it,
///   in source order and each once; a suspended one gives none.
/// - provides: the `explicit-runs` lint's findings, before a verb filters them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nested calls in three declarations of a strict source,
///   each listed once, in source order, and reported where a lint reaches it.
/// - witness: `entry::tests::an_inferred_run_is_reported_where_a_lint_reaches`
#[spec(ensures: |ret| ret.is_sorted() && ret.windows(2_usize).all(|pair| pair.first() != pair.get(1_usize)))]
fn inferred_runs(
    module: &LoweredModule<'_>,
    verdicts: &ModuleReport,
) -> Vec<InferredRun>
{
    module.inferred_runs(
        verdicts
            .nested_elaborations()
            .values()
            .flat_map(|elaboration| {
                elaboration
                    .decisions()
                    .iter()
                    .filter_map(|(&at, &decided)| match decided {
                        Nesting::Ran(purity) => Some((at, purity)),
                        Nesting::Returned => Some((at, gandr_core_term::effect::Purity::Pure)),
                        Nesting::Suspended => None,
                    })
            }),
    )
}

/// The lowering's origin table, with every node the checker's elaborations of
/// the declarations from `from` on minted located at the written node it
/// elaborates.
///
/// A body holding a computation written where a value is read is judged
/// twice, and the verdict is the second run's, over the elaborated body: a
/// refusal or a frame of that run names elaborated nodes, which the lowering
/// never minted. Each is published at the written node that elaborated: a
/// rebuilt node at the node it was rebuilt from, so the respect check of a
/// case whose arms nest a call refuses at the case as its bound spelling
/// does, and a bind minted for a run at the nested call it runs.
///
/// # Specification
/// - requires: `origins` is the table of the module `verdicts` judged, read
///   before any node the elaborations of the declarations from `from` on minted
///   was recorded in it, those of the declarations before `from` located
///   already ([`ClosureLowering::resume_onto`]).
/// - ensures: `origins` with [`OriginTable::carry`] applied to what
///   [`elaborated`] answers of `verdicts` from `from`; `origins` itself when no
///   body from `from` on was elaborated.
/// - provides: the table a second-run refusal is located through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fold nesting its call and its bound twin, each refused
///   by the rule it tells apart, refuse at one case block; a closure's fold and
///   a document's nested call, judged on a held closure, locate as on a fresh
///   one.
/// - witness: `entry::tests::a_second_run_refusal_is_located_where_its_bound_spelling_is_380`
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[spec(captures: [declarations = origins.declaration_count(), recorded = origins.recorded_count()],
    ensures: origins.declaration_count() == declarations && origins.recorded_count() >= recorded)]
fn located(
    origins: &mut OriginTable,
    verdicts: &ModuleReport,
    from: ConstantIndex,
)
{
    let (carried, binds) = elaborated(verdicts, from);
    origins.carry(&carried, &binds);
}

/// What the checker's elaborations of `verdicts`' declarations from `from` on
/// minted: each node beside the node it stands for, and each bind minted for
/// a run beside its run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every carried pair, then every bind, of the nested elaboration of
///   each declaration at or after `from`, in admission order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`located`].
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[spec(ensures: |ret| {
    let elaborations = verdicts.nested_elaborations().range(from ..);
    ret.0.len() == elaborations.clone().map(|(_, elaboration)| elaboration.carried().len()).sum::<usize>()
        && ret.1.len() == elaborations.map(|(_, elaboration)| elaboration.binds().len()).sum::<usize>()
})]
fn elaborated(
    verdicts: &ModuleReport,
    from: ConstantIndex,
) -> (Vec<Carried>, Vec<(ValueId, ComputationId)>)
{
    let elaborations = verdicts.nested_elaborations().range(from ..);
    let carried = elaborations
        .clone()
        .flat_map(|(_, elaboration)| elaboration.carried().iter().copied())
        .collect();
    let binds = elaborations
        .flat_map(|(_, elaboration)| elaboration.binds().iter().copied())
        .collect();
    (carried, binds)
}

/// Judge one lowered module: the second half of the composition.
///
/// # Specification
/// - requires: the module was lowered from its text into `arena`; `root` is the
///   corpus root the source sits under.
/// - ensures: [`judge`] under `grant`, then [`Judged::admit`]: the result is
///   [`Composed::Settled`] with one report per declared name, the exercised
///   rows its settled declarations carry, the refusals of the declarations
///   refused at their own form, which no expectation can state, the lowering's
///   origin table, moved rather than copied, the kernel artifact of every
///   declaration that crossed, under the module's structured names, and the
///   program.
/// - provides: the verdict set [`compose()`] gives a module the lowering read.
/// - fails: [`ComposeFault::Readmission`] for a declaration the checker
///   accepted that the kernel does not re-derive; else [`ComposeFault::Settle`]
///   when the settle comparison refuses the verdicts.
/// - panics: none.
///
/// # Errors
/// - [`ComposeFault::Readmission`]: the kernel disagreed with the checker.
/// - [`ComposeFault::Settle`]: the verdicts are not the module's own.
///
/// # Adequacy
/// - hypothesis: L3 literal declaration names, verdicts, refusal positions and
///   kernel-export names distinguish omission, reordering and wrong routing in
///   finite mixed modules. L2 kernel re-derivation supplies a second checker
///   for acceptances, not a proof for all programs or kernel failures.
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `compose::tests::the_root_decides_what_an_expectation_means`
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
/// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
#[inline]
#[spec(
    captures: [
        expected_declarations = module.declarations().len(),
        expected_unstatable = module.declarations().iter().filter(|declaration|
            matches!((declaration.outcome(), declaration.signature(), declaration.definition()),
                (DeclarationOutcome::Refused(_), Maybe::Absent(_), Maybe::Absent(_))))
            .count(),
    ],
    ensures: |ref ret| match *ret {
        Ok(Composed::Settled { ref report, ref unstatable, ref kernel, .. }) =>
            report.declarations().len() == expected_declarations
                && unstatable.len() == expected_unstatable
                && matches!(kernel, Maybe::Present(_)),
        Err(ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => true,
        Ok(Composed::Refused(_)) | Err(ComposeFault::Parse(_) | ComposeFault::Lowering(_)) => false,
    },
)]
pub fn judge_module<'source>(
    root: CorpusRoot,
    (module, text): (LoweredModule<'source>, SourceText<'source>),
    arena: CoreArena,
    grant: &HostGrant,
) -> Result<Composed<'source>, ComposeFault<'source>>
{
    judge(root, (module, text), arena, grant).admit()
}

/// Carry one source through the pipeline: parse, lower, adapt, check, settle.
///
/// # Specification
/// - requires: `grammar` is the checked grammar the source is parsed under;
///   `root` is the corpus root the source sits under.
/// - ensures: [`lower_source`] then, for a module the lowering read,
///   [`judge_module`] under no grant: after parsing succeeds, the source is
///   lowered once and `lowerings` advances once, saturating; a parse failure
///   leaves it unchanged. A read module is [`Composed::Settled`] with one
///   report per declared name; an author or fragment refusal of the whole
///   source is [`Composed::Refused`].
/// - provides: the one verdict set a run gives the source, whichever verb runs
///   it.
/// - fails: as [`lower_source`] and [`judge_module`].
/// - panics: none.
/// - intension: one parse, one lowering, one judgement, one readmission and one
///   settle per source; [`LoweringCount`] is the declared projection of the
///   lowering half.
///
/// # Errors
/// - [`ComposeFault::Parse`]: the tree could not be committed.
/// - [`ComposeFault::Lowering`]: the lowering faulted before any declaration
///   could be trusted.
/// - [`ComposeFault::Readmission`]: the kernel disagreed with the checker.
/// - [`ComposeFault::Settle`]: the verdicts are not the module's own.
///
/// # Adequacy
/// - hypothesis: L3 exact declaration outcomes and lowering counts separate
///   ordinary modules, whole-source refusals, root policies and saturation. L2
///   kernel re-derivation checks agreement on acceptances. The finite sources
///   do not establish arbitrary program correctness or parser-failure coverage.
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`
/// - witness: `compose::tests::each_composition_lowers_once`
/// - witness: `compose::tests::the_root_decides_what_an_expectation_means`
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
/// - witness: `script::tests::run_source_counts_lowerings_with_saturation`
#[inline]
#[spec(
    captures: [before = lowerings.0],
    ensures: |ref ret| lowerings.0 == if matches!(ret, Err(ComposeFault::Parse(_))) {
        before
    } else {
        before.saturating_add(1)
    } && match *ret {
        Ok(Composed::Refused(refusal)) => refusal.classify() != FailureClass::EngineFault,
        Err(ComposeFault::Lowering(refusal)) => refusal.classify() == FailureClass::EngineFault,
        Ok(Composed::Settled { .. })
            | Err(ComposeFault::Parse(_) | ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => true,
    },
)]
pub fn compose<'source>(
    grammar: &Pbg,
    root: CorpusRoot,
    source: SourceText<'source>,
    lowerings: &mut LoweringCount,
) -> Result<Composed<'source>, ComposeFault<'source>>
{
    let lowering = lower_source(grammar, source, lowerings)?;
    judge_lowering(
        root,
        (lowering, source),
        &HostGrant::UNBOUNDED,
        ByteOffset::from(0_usize),
    )
}

/// Judge what the lowering made of one source, its obligations given up.
///
/// # Specification
/// - requires: the lowering read the text beside it; `root` is the corpus root
///   the source sits under.
/// - ensures: a module the lowering read is judged by [`judge_member`] at
///   `base` under `grant` and admitted; a whole-source refusal is
///   [`Composed::Refused`].
/// - provides: the half of [`compose()`] that stays in walk order when a wider
///   walk lowers its sources on several threads.
/// - fails: as [`judge_module`].
/// - panics: none.
///
/// # Errors
/// - [`ComposeFault::Readmission`]: the kernel disagreed with the checker.
/// - [`ComposeFault::Settle`]: the verdicts are not the module's own.
///
/// # Adequacy
/// - hypothesis: L3 — the composition witnesses route modules and whole
///   refusals through here, and the corpus at several widths composes equal to
///   the serial walk.
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
#[inline]
#[spec(
    captures: [refused = matches!(lowering.lowered, Lowered::Refused(_))],
    ensures: |ref ret| match *ret {
        Ok(Composed::Refused(_)) => refused,
        Ok(Composed::Settled { .. }) | Err(ComposeFault::Readmission(_) | ComposeFault::Settle(_)) => !refused,
        Err(ComposeFault::Parse(_) | ComposeFault::Lowering(_)) => false,
    },
)]
pub fn judge_lowering<'source>(
    root: CorpusRoot,
    (lowering, text): (Lowering<'source>, SourceText<'source>),
    grant: &HostGrant,
    base: ByteOffset,
) -> Result<Composed<'source>, ComposeFault<'source>>
{
    match lowering.into_lowered() {
        Lowered::Module { module, arena } => {
            judge_member(root, (module, text), arena, grant, base).admit()
        },
        Lowered::Refused(refusal) => Ok(Composed::Refused(refusal)),
    }
}

/// The refusals of declarations refused at their own form, in admission order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: retains exactly the refusal of each declaration with neither a
///   signature nor a definition, in the module's order; other declarations
///   contribute nothing.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — refused forms surround a refused body and an admitted
///   definition; exact refusal values and their distinct spans distinguish
///   inclusion, omission and reversal. This covers the admission-order filter,
///   not the lowering's reasons for rejecting arbitrary syntax.
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
/// - witness: `compose::tests::form_refusals_retain_admission_order`
#[spec(ensures: |ref ret| {
    let mut selected = ret.iter();
    module.declarations().iter().all(|declaration| {
        match (declaration.outcome(), declaration.signature(), declaration.definition()) {
            (DeclarationOutcome::Refused(refusal), Maybe::Absent(_), Maybe::Absent(_)) =>
                selected.next() == Some(&refusal),
            _ => true,
        }
    }) && selected.next().is_none()
})]
fn unstatable<'source>(module: &LoweredModule<'source>) -> Vec<LoweringRefusal<'source>>
{
    module
        .declarations()
        .iter()
        .filter_map(|lowered| {
            match (lowered.outcome(), lowered.signature(), lowered.definition()) {
                (DeclarationOutcome::Refused(refusal), Maybe::Absent(_), Maybe::Absent(_)) => {
                    Some(refusal)
                },
                (DeclarationOutcome::Refused(_), Maybe::Present(_), _)
                | (DeclarationOutcome::Refused(_), _, Maybe::Present(_))
                | (
                    DeclarationOutcome::Completed { .. }
                    | DeclarationOutcome::Uncompleted { .. }
                    | DeclarationOutcome::Bodied { .. }
                    | DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Codata(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World,
                    ..,
                ) => None,
            }
        })
        .collect()
}

/// The worlds `module` declares, by name: what a host's named entry is read
/// against.
///
/// # Specification
/// - ensures: one entry per world declaration, its name to its admission
///   position; a name declared twice keeps the later position, which the
///   lowering has already refused as a duplicate.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module declaring two worlds beside other declarations,
///   read under a host entry naming them, enters at them; a name it does not
///   declare grants nothing.
/// - witness: `compose::tests::a_host_entry_names_the_worlds_a_module_declares`
#[spec(ensures: |ref ret| ret.len() <= module.declarations().len())]
fn declared_worlds(module: &LoweredModule<'_>) -> BTreeMap<WorldName, ConstantIndex>
{
    module
        .declarations()
        .iter()
        .filter(|declaration| matches!(declaration.outcome(), DeclarationOutcome::World))
        .map(|declaration| {
            (
                WorldName::from(declaration.name().as_ref()),
                declaration.constant(),
            )
        })
        .collect()
}

/// The holes `module`'s matches were written with in place of a pattern: what
/// the checker refuses at a match tree's leaf.
///
/// # Specification
/// trivial.
fn pattern_holes(module: &LoweredModule<'_>) -> Vec<HoleId>
{
    module
        .origins()
        .cases()
        .flat_map(|(_, case)| case.patterns.holes())
        .collect()
}

/// The checker the formatter's meaning check asks for elaborated bodies: a
/// lowered module judged whole, as [`judge`] judges one under the unbounded
/// grant, entering at the worlds it declares.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`gandr_surface_format::Elaborate`]: for each declaration of
///   the module, in its order, the body the checker defines for it — a nested
///   computation elaborated to the bind it runs as — and none for one it
///   refuses, defines nothing for, or the lowering refused.
/// - provides: the checker half of `gandr fmt`'s meaning check.
/// - fails: never; a refusal is a declaration with no body.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `run` statement read once first and the call written at
///   its read elaborate to one body, so the sugared form writes it away, and so
///   do a `thunk { e }` and the `e` the checker wraps in one where it checks
///   `e` against a thunk type; a source formatted without the checker keeps
///   both.
/// - witness: `format::tests::a_linear_run_is_written_away_beside_a_checker`
/// - witness: `format::tests::a_thunk_the_checker_inserts_is_left_to_it_1327`
#[derive(Clone, Copy, Debug, Default)]
pub struct Elaborating;

impl gandr_surface_format::Elaborate for Elaborating
{
    /// Check `module` beside the host's built-ins and answer each
    /// declaration's elaborated body, as [`Elaborating`] states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn definitions(
        &self,
        arena: &mut CoreArena,
        module: &LoweredModule<'_>,
    ) -> Vec<Option<ValueId>>
    {
        let grant = HostGrant::UNBOUNDED;
        let declarations = adapt(module);
        let entry = grant.entry(&declared_worlds(module));
        let grants = grant.grants(arena);
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        context.grant(grants);
        context.enter_at(entry);
        context.keep_pattern_holes(&pattern_holes(module));
        let report = check_module(&mut context, &declarations);
        let definitions = report.definitions();
        module
            .declarations()
            .iter()
            .map(|declaration| definitions.get(&declaration.constant()).copied())
            .collect()
    }
}

/// The checker's input for `module`: every declaration the lowering did not
/// refuse, in admission order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Declaration`] per unrefused declaration, in admission
///   order, at the same position and with the lowering's origin as its token: a
///   completed declaration carries its declared type and its body, an
///   uncompleted one its declared type and a hole, a bodiless definition its
///   body and no signature, each of the three the laws its `respects` attribute
///   names and the entry its `entry` attribute names; a data declaration
///   carries its native signature and a codata declaration its decoded one,
///   each shared with the lowered module, a sealed abstract type its kind,
///   representation, extent, site, mobility and the interface its type member's
///   `identity` attribute names, and a world declaration nothing but its
///   position. A refused declaration is not offered.
/// - provides: the one place that names both the lowering's module and the
///   checker's declaration input.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a real module settles each declaration once, retaining
///   source order across accepted and refused declarations. This observes the
///   composed judgement rather than a copy of the adapter match.
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
/// - witness: `compose::tests::a_sealed_module_settles_its_abstract_type`
#[inline]
#[must_use]
#[spec(ensures: |ref ret| {
    let mut expected = module.declarations().iter().filter(|declaration|
        !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)));
    ret.iter().all(|actual| expected.next().is_some_and(|lowered| {
        actual.constant() == lowered.constant()
            && usize::from(actual.origin()) == usize::from(lowered.origin())
            && actual.laws() == module.laws(lowered)
            && actual.stages() == module.stages(lowered)
            && actual.supplies() == module.supplies(lowered)
            && match lowered.outcome() {
                DeclarationOutcome::Completed { declared_type, body } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(declared_type),body:Maybe::Present(body)},
                DeclarationOutcome::Uncompleted { declared_type } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(declared_type),body:Maybe::Absent(body::Absent::Hole)},
                DeclarationOutcome::Bodied { body } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Absent(signature::Absent::Unsigned),body:Maybe::Present(body)},
                DeclarationOutcome::Data(index) =>
                    matches!(*actual.content(), gandr_core_checker::DeclarationContent::Data(ref held) if module.data(index) == Maybe::Present(held)),
                DeclarationOutcome::Codata(index) =>
                    matches!(*actual.content(), gandr_core_checker::DeclarationContent::Codata(ref held) if module.codata(index) == Maybe::Present(held)),
                DeclarationOutcome::Abstract(sealing) =>
                    *actual.content() == gandr_core_checker::DeclarationContent::Abstract(abstract_type(sealing, module.interface(lowered))),
                DeclarationOutcome::World =>
                    *actual.content() == gandr_core_checker::DeclarationContent::World,
                DeclarationOutcome::Refused(_) => false,
            }
    })) && expected.next().is_none()
})]
pub fn adapt(module: &LoweredModule<'_>) -> Vec<Declaration>
{
    let mut declarations = Vec::with_capacity(module.declarations().len());
    for lowered in module.declarations() {
        let (declared, defined) = match lowered.outcome() {
            DeclarationOutcome::Completed {
                declared_type,
                body,
            } => (Maybe::Present(declared_type), Maybe::Present(body)),
            DeclarationOutcome::Uncompleted { declared_type } => (
                Maybe::Present(declared_type),
                Maybe::Absent(body::Absent::Hole),
            ),
            DeclarationOutcome::Bodied { body } => (
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(body),
            ),
            DeclarationOutcome::Data(index) => {
                if let Maybe::Present(signature) = module.data(index) {
                    declarations.push(Declaration::data(
                        lowered.constant(),
                        Arc::clone(signature),
                        OriginToken::from(usize::from(lowered.origin())),
                    ));
                }
                continue;
            },
            DeclarationOutcome::Codata(index) => {
                if let Maybe::Present(signature) = module.codata(index) {
                    declarations.push(Declaration::codata(
                        lowered.constant(),
                        Arc::clone(signature),
                        OriginToken::from(usize::from(lowered.origin())),
                    ));
                }
                continue;
            },
            DeclarationOutcome::Abstract(sealing) => {
                declarations.push(Declaration::abstract_type(
                    lowered.constant(),
                    abstract_type(sealing, module.interface(lowered)),
                    OriginToken::from(usize::from(lowered.origin())),
                ));
                continue;
            },
            DeclarationOutcome::World => {
                declarations.push(Declaration::world(
                    lowered.constant(),
                    OriginToken::from(usize::from(lowered.origin())),
                ));
                continue;
            },
            DeclarationOutcome::Refused(_) => continue,
        };
        let declaration = Declaration::new(
            lowered.constant(),
            declared,
            defined,
            OriginToken::from(usize::from(lowered.origin())),
        )
        .lawful(module.laws(lowered).to_vec())
        .ruled(module.operation_rules(lowered))
        .staged(module.stages(lowered).to_vec())
        .supplied(module.supplies(lowered).to_vec());
        declarations.push(match Entry::declared(module.worlds(lowered)) {
            Maybe::Present(entry) => declaration.entered(entry),
            Maybe::Absent(_) => declaration,
        });
    }
    declarations
}

/// The checker's abstract type for the sealing the lowering recorded: its
/// kind, representation and extent, at the site its sealing module and
/// component number, mobile exactly when its signature marks it, relating
/// its elements by the `members` its type member's `identity` names.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — three members, two and none give a lawful, a lawless and
///   a plain atom, which read the relation's evidence apart.
/// - witness: `compose::tests::a_sealed_atom_s_identity_decides_what_its_relation_s_evidence_is`
/// - witness: `compose::tests::a_sealed_module_settles_its_abstract_type`
fn abstract_type(
    sealing: Sealing,
    members: &[ValueId],
) -> AbstractType
{
    let sealed = AbstractType::new(
        sealing.kind,
        sealing.representation,
        sealing.extent,
        SealSite::new(
            SealingSite::from(usize::from(sealing.sealing)),
            ComponentOrdinal::from(usize::from(sealing.component)),
        ),
    )
    .marked(match sealing.mark {
        Mark::Unmarked => Mobility::Immobile,
        Mark::Mobile => Mobility::Mobile,
    });
    match *members {
        [relation, reflexivity] => sealed.interfaced(AtomInterface::new(relation, reflexivity)),
        [relation, reflexivity, law] => {
            sealed.interfaced(AtomInterface::new(relation, reflexivity).lawful(law))
        },
        _ => sealed,
    }
}

/// What [`readmitted`] answers: the readmission or the first disagreement,
/// beside the record of its boundary; or the retirement, beside the record of
/// the declarations crossed before it.
type Readmitting<Retired> = Polled<
    (
        Result<bridge::Readmission, bridge::Readmitted>,
        Maybe<bridge::Crossed, bridge::crossed::Absent>,
    ),
    Retired,
    Maybe<bridge::Crossed, bridge::crossed::Absent>,
>;

/// Have the kernel re-derive every declaration in `verdicts` the checker
/// accepted, resuming the first of them from `leading`'s record and
/// recording its boundary's, as [`bridge::readmit_retiring`] does under
/// `retirement`.
///
/// # Specification
/// - requires: `verdicts` was judged over `arena`; `leading`'s record, when
///   present, as [`bridge::readmit_resuming`] requires.
/// - ensures: retired before a declaration, [`bridge::readmit_retiring`]'s
///   retirement and record. Otherwise, beside [`bridge::readmit_resuming`]'s
///   record of `leading`'s boundary, succeeds with the readmission when every
///   accepted declaration crossed as a definition or an axiom, or stays on the
///   checker's side as a static definition or as an effectful one the bridge
///   refuses by its effectful former; a refused declaration crosses as its
///   mark, a suspended one crosses as nothing until a fill resumes it, a
///   declaration withheld because it names a refused one carries that one's
///   reason, a declaration holding a term hole or the unknown type stays behind
///   as the user absence it is, and a declaration holding a session stays
///   behind on the checker's side, the kernel having no session former, so none
///   of these is a disagreement.
/// - provides: the kernel's repetition of every acceptance a run reports, and
///   the environment the run's kernel artifact is exported from.
/// - fails: the readmission of the first declaration the kernel rejected or the
///   bridge refused for any reason but a withheld constant, a user absence, a
///   session or an effectful former.
/// - panics: none.
///
/// # Errors
/// The readmission of the first declaration the kernel did not re-derive.
///
/// # Adequacy
/// - hypothesis: L3 — a mark, withheld reference and definition are admitted
///   over their own arena. A foreign arena exposes the checked reference's
///   dangling ids at the first nonzero failure position. Kernel-export names
///   also observe an axiom crossing, and an exercise and a scope stay checked
///   beside a readmitted definition. These cases do not exercise every bridge
///   refusal or certificate rejection.
/// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
/// - witness: `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`
/// - witness: `compose::tests::an_effectful_declaration_stays_on_the_checkers_side`
#[spec(ensures: |ref ret| match *ret {
    Polled::Retired(..) => true,
    Polled::Whole((ref whole, _)) => match *whole {
    Ok(ref readmission) => readmission.readmitted().len() == verdicts.judged().len()
        && readmission.readmitted().iter().zip(verdicts.judged()).all(|(crossed, judged)|
            crossed.constant() == judged.constant() && (matches!(*crossed.outcome(),
                bridge::Outcome::Defined { .. } | bridge::Outcome::Assumed { .. }
                    | bridge::Outcome::Data { .. }
                    | bridge::Outcome::Marked(_) | bridge::Outcome::Suspended | bridge::Outcome::Static
                    | bridge::Outcome::Refused(bridge::Refusal::Withheld { .. } | bridge::Refusal::WithheldData { .. }
                        | bridge::Refusal::Hole { .. } | bridge::Refusal::Unknown { .. }
                        | bridge::Refusal::Session { .. } | bridge::Refusal::Located { .. }))
                || matches!(*crossed.outcome(), bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }) if residence(former) == Residence::Checker))),
    Err(ref fault) =>
        verdicts.judged().iter().any(|judged| judged.constant() == fault.constant())
            && (matches!(*fault.outcome(), bridge::Outcome::Rejected(_)
                | bridge::Outcome::Refused(bridge::Refusal::DanglingNode { .. }
                    | bridge::Refusal::Cyclic { .. } | bridge::Refusal::CertificateDeclined { .. }
                    | bridge::Refusal::MachineInvariant))
                || matches!(*fault.outcome(), bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }) if residence(former) == Residence::Kernel)),
    },
})]
fn readmitted<Poll>(
    arena: &mut CoreArena,
    verdicts: &ModuleReport,
    leading: (
        bridge::LeadingCount,
        Maybe<&bridge::Crossed, bridge::crossed::Absent>,
    ),
    retirement: &Poll,
) -> Readmitting<Poll::Retired>
where
    Poll: Retirement,
{
    let (boundary, crossed) = leading;
    let (readmission, recorded) =
        match bridge::readmit_retiring(arena, verdicts, boundary, crossed, retirement) {
            Polled::Whole(whole) => whole,
            Polled::Retired(retired, held) => return Polled::Retired(retired, held),
        };
    for readmitted in readmission.readmitted() {
        match *readmitted.outcome() {
            bridge::Outcome::Data { .. }
            | bridge::Outcome::Defined { .. }
            | bridge::Outcome::Assumed { .. }
            | bridge::Outcome::Marked(_)
            | bridge::Outcome::Suspended
            | bridge::Outcome::Static
            | bridge::Outcome::Refused(
                bridge::Refusal::Withheld { .. }
                | bridge::Refusal::WithheldData { .. }
                | bridge::Refusal::Hole { .. }
                | bridge::Refusal::Unknown { .. }
                | bridge::Refusal::Session { .. }
                | bridge::Refusal::Located { .. },
            ) => {},
            bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. })
                if residence(former) == Residence::Checker => {},
            bridge::Outcome::Refused(
                bridge::Refusal::OutOfFragment { .. }
                | bridge::Refusal::DanglingNode { .. }
                | bridge::Refusal::Cyclic { .. }
                | bridge::Refusal::CertificateDeclined { .. }
                | bridge::Refusal::MachineInvariant,
            )
            | bridge::Outcome::Rejected(_) => {
                return Polled::Whole((Err(readmitted.clone()), recorded));
            },
        }
    }
    Polled::Whole((Ok(readmission), recorded))
}

/// Which side of the boundary a declaration holding a former the kernel has
/// no rule for belongs on.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Residence
{
    /// The former is effectful and the kernel pure by design: the declaration
    /// stays on the checker's side.
    Checker,
    /// The former is pure: the kernel is meant to admit it, so the bridge's
    /// refusal is a disagreement.
    Kernel,
}

/// The side of the boundary a declaration the bridge refuses for `former`
/// belongs on.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the checker's side for an effect row, a stack and its literal, a
///   request, a handler, a resumption, a delimiter, a capture, a capability, an
///   exercise, a scope, a recorded run or ride and a memory form; the kernel's
///   for every pure former, and for a recursion's stage, which no source writes
///   and the checker never lets a declaration carry, so its refusal is the
///   checker's fault.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module holding a capability, its exercise and its scope
///   settles with nothing crossed for them, while a foreign arena's refusal is
///   still a fault.
/// - witness: `compose::tests::an_effectful_declaration_stays_on_the_checkers_side`
/// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
#[spec(ensures: |ret| (ret == Residence::Kernel) == matches!(former,
    UnadmittedFormer::ValueLift | UnadmittedFormer::NumericLiteral | UnadmittedFormer::NumericAtom
        | UnadmittedFormer::TypeLift | UnadmittedFormer::Abstract | UnadmittedFormer::SortParameter
        | UnadmittedFormer::TopUniverse | UnadmittedFormer::StaticLambda | UnadmittedFormer::Stage))]
fn residence(former: UnadmittedFormer) -> Residence
{
    match former {
        UnadmittedFormer::EffectRow
        | UnadmittedFormer::Reify
        | UnadmittedFormer::Stack
        | UnadmittedFormer::Perform
        | UnadmittedFormer::Handle
        | UnadmittedFormer::Resume
        | UnadmittedFormer::Abandon
        | UnadmittedFormer::Reset
        | UnadmittedFormer::Shift
        | UnadmittedFormer::Capability
        | UnadmittedFormer::Exercise
        | UnadmittedFormer::Scope
        | UnadmittedFormer::Run
        | UnadmittedFormer::Memory
        | UnadmittedFormer::Buffer => Residence::Checker,
        UnadmittedFormer::ValueLift
        | UnadmittedFormer::NumericLiteral
        | UnadmittedFormer::NumericAtom
        | UnadmittedFormer::TypeLift
        | UnadmittedFormer::Abstract
        | UnadmittedFormer::SortParameter
        | UnadmittedFormer::TopUniverse
        | UnadmittedFormer::StaticLambda
        | UnadmittedFormer::Stage => Residence::Kernel,
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Demand;
    use gandr_core_checker::HostGrant;
    use gandr_core_checker::ObligationCount;
    use gandr_core_checker::Polled;
    use gandr_core_checker::Retirement;
    use gandr_core_checker::Unretired;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_checker::worlds::WorldName;
    use gandr_core_term::CertificateEquality;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Value;
    use gandr_core_term::equal_certificate_syntax;
    use gandr_core_term::equal_type_syntax;
    use gandr_kernel_term::decode;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Produced;
    use gandr_surface_corpus::RefusalName;
    use gandr_surface_corpus::Settlement;
    use gandr_surface_corpus::settle;
    use gandr_surface_diagnostics::constant_names;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::DeclarationOutcome;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_pretty::CoreNode;
    use gandr_surface_pretty::CoreSource;
    use gandr_surface_pretty::Fidelity;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::Name;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_pretty::Restoration;
    use gandr_surface_pretty::present_computation;
    use gandr_surface_pretty::present_type;
    use gandr_surface_pretty::present_value;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::ComposeFault;
    use super::Composed;
    use super::Lowered;
    use super::LoweringCount;
    use super::adapt;
    use super::admitted;
    use super::compose;
    use super::judge;
    use super::judge_module;
    use super::lower_source;
    use super::readmitted;
    use crate::evaluate::Program;
    use crate::exercised::Exercised;

    /// The built-in grammar.
    ///
    /// # Specification
    /// - requires: the built-in grammar can be constructed.
    /// - ensures: returns that checked grammar, including candidates for the
    ///   declaration keyword `def`.
    /// - fails: never.
    /// - panics: if the built-in grammar is invalid.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed declarations and a whole-source refusal are
    ///   interpreted with exact expected outcomes. These fixtures detect an
    ///   unusable or incompatible grammar, not equivalence over all syntax.
    /// - witness: `compose::tests::a_module_settles_every_declaration_once`
    /// - witness: `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`
    #[spec(ensures: |ref ret|
        !ret.candidates(gandr_surface_grammar::TileLabel("def")).is_empty())]
    fn grammar() -> Pbg
    {
        built_in().expect("the built-in grammar builds")
    }

    /// #1033: an import closure lowered once is counted by its own sources;
    /// each document resumed on it is counted by the document's sources and
    /// lowers as the whole unit lowers over the same parse; a closure that
    /// ends inside a token is not held, and counts nothing.
    #[test]
    fn a_closure_lowers_once_and_resumes_per_document_1033()
    {
        use alloc::string::String;
        use alloc::sync::Arc;

        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::LoweredModule;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_parser::Unlayable;
        use gandr_surface_syntax::ByteOffset;

        use super::Lowering;
        use super::Unheld;
        use super::lower_closure;
        use super::lower_parsed_unit;
        use super::lower_resumed_unit;

        /// The module and arena `lowering` lowered to.
        ///
        /// # Specification
        /// trivial.
        fn module(lowering: Lowering<'_>) -> (LoweredModule<'_>, CoreArena)
        {
            match lowering.into_lowered() {
                Lowered::Module { module, arena } => (module, arena),
                Lowered::Refused(refusal) => panic!("refused whole: {refusal}"),
            }
        }

        let pbg = grammar();
        let closure_text = "def one : Integer ;\ndef one = 1 ;\n";
        let own = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        let text = format!("{closure_text}{own}");
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(ByteOffset::from(closure_text.len()), vec![
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ]),
        ])
        .expect("two sources make a unit");
        let alone = || {
            Unit::new(vec![UnitSource::new(ByteOffset::from(0_usize), Vec::new())])
                .expect("one source makes a unit")
        };
        let mut lowerings = LoweringCount::default();
        let closure = lower_closure(
            Arc::new(grammar()),
            String::from(closure_text),
            alone(),
            &mut lowerings,
        )
        .expect("the closure is held");
        assert_eq!(
            lowerings,
            LoweringCount::from(1_usize),
            "the closure's one source"
        );
        for resumed in 1_usize ..= 2_usize {
            let parsed = parse(&pbg, SourceText::from(own))
                .expect("the document parses")
                .after(closure.tree(), SourceText::from(text.as_str()))
                .expect("the document lays after its closure");
            let whole = lower_parsed_unit(
                &pbg,
                parsed.clone(),
                &unit,
                &mut LoweringCount::default(),
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the whole unit lowers");
            let resumed_lowering = lower_resumed_unit(
                &closure,
                parsed,
                &unit,
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the document lowers resumed");
            assert_eq!(
                module(resumed_lowering),
                module(whole),
                "the module and arena the whole unit lowers to"
            );
            assert_eq!(
                lowerings,
                LoweringCount::from(resumed.saturating_add(1_usize)),
                "each resume counts the document's one source"
            );
        }
        let mut untouched = LoweringCount::default();
        assert_eq!(
            lower_closure(
                Arc::new(grammar()),
                String::from("def one = 1 ;\n/* never closed"),
                alone(),
                &mut untouched,
            )
            .map(|_held| ()),
            Err(Unheld::Unlayable(Unlayable::Open)),
            "a closure that ends inside a comment is not held"
        );
        assert_eq!(untouched, LoweringCount::default(), "and counts nothing");
    }

    /// #776: a closure judged once judges each document laid after it as a
    /// closure judged fresh for that document does — two revisions in turn,
    /// then the first again — down to the composition and the kernel's
    /// artifact, each lowering counted by the document's own source; and each
    /// reports of its own declarations what the whole unit, lowered and judged
    /// whole, reports: their names, spans, statements, debts, waits, the kind
    /// of each verdict, each outcome — a run of a closure's constant included —
    /// and the spelling of each type a refusal compares, the closure refusing
    /// one of its own declarations at its lowering and one at its check; and
    /// every node the closure's fold elaborated from a located node is located
    /// in the document's table, the document's own nested call carried after
    /// its lowering.
    #[test]
    fn a_closure_judged_once_judges_each_document_alike_776()
    {
        use alloc::string::String;
        use alloc::sync::Arc;
        use core::mem::Discriminant;

        use gandr_core_term::Carried;
        use gandr_surface_corpus::Outcome;
        use gandr_surface_corpus::Refusal;
        use gandr_surface_corpus::Stated;
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::LoweredModule;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::SurfaceName;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_pretty::Spelling;
        use gandr_surface_syntax::ByteOffset;
        use gandr_surface_syntax::ByteSpan;

        use super::Checking;
        use super::Judged;
        use super::JudgedClosure;
        use super::Lowering;
        use super::judge_member;
        use super::judge_member_after;
        use super::lower_closure;
        use super::lower_onto_closure;
        use super::lower_parsed_unit;

        /// One declaration's report: its name, span, statement, debt, waits,
        /// the kinds of what it produced and of its verdict, its outcome and
        /// the spellings of the types its refusal compares.
        type Reported<'source> = (
            SurfaceName<'source>,
            ByteSpan,
            Stated,
            ObligationCount,
            Vec<SurfaceName<'source>>,
            (
                Discriminant<Produced<'source>>,
                Option<Discriminant<Verdict>>,
            ),
            (Outcome, Vec<String>),
        );

        /// The module and arena `lowering` lowered to.
        ///
        /// # Specification
        /// trivial.
        fn module(lowering: Lowering<'_>) -> (LoweredModule<'_>, CoreArena)
        {
            match lowering.into_lowered() {
                Lowered::Module { module, arena } => (module, arena),
                Lowered::Refused(refusal) => panic!("refused whole: {refusal}"),
            }
        }

        /// `own`, laid after `judged`'s closure in `text` as `unit` lays it
        /// out from `base`, lowered after `judged`'s arena and judged after
        /// it.
        ///
        /// # Specification
        /// trivial.
        fn after<'held>(
            judged: &'held JudgedClosure,
            (own, text): (SourceText<'held>, SourceText<'held>),
            (unit, base): (&Unit, ByteOffset),
            lowerings: &mut LoweringCount,
        ) -> Judged<'held>
        {
            let closure = judged.lowering();
            let parsed = parse(closure.grammar(), own)
                .expect("the document parses")
                .after(closure.tree(), text)
                .expect("the document lays after its closure");
            let (lowering, checking) = lower_onto_closure(
                judged,
                judged.arena(),
                parsed,
                unit,
                lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the document lowers");
            assert!(
                matches!(checking, Checking::After(_)),
                "the document is judged after the closure"
            );
            let (module, arena) = module(lowering);
            judge_member_after(
                CorpusRoot::Strict,
                (module, text),
                arena,
                (&HostGrant::UNBOUNDED, checking),
                base,
            )
        }

        /// Each declaration `judged` reports, its ids set aside.
        ///
        /// # Specification
        /// trivial.
        fn reported(judged: Judged<'_>) -> Vec<Reported<'_>>
        {
            let Ok(Composed::Settled {
                report, spellings, ..
            }) = judged.settled
            else {
                panic!("the document settles");
            };
            let spelled = spellings.spelled(Spelling::Unicode);
            report
                .declarations()
                .iter()
                .map(|declaration| {
                    let produced = declaration.produced();
                    let verdict = match produced {
                        Produced::Judged(verdict) => Some(core::mem::discriminant(&verdict)),
                        Produced::Unlowered(_) | Produced::Guarded(_) => None,
                    };
                    let compared = match produced.refusal() {
                        Maybe::Present(Refusal::Checking(refusal)) => {
                            let compared = refusal.compared();
                            [compared.expected, compared.found]
                                .into_iter()
                                .map(|side| match side {
                                    Maybe::Present(node) => match spelled.get(node) {
                                        Maybe::Present(spelling) => String::from(spelling.as_ref()),
                                        Maybe::Absent(_) => String::from("unspelled"),
                                    },
                                    Maybe::Absent(_) => String::from("absent"),
                                })
                                .collect()
                        },
                        Maybe::Present(Refusal::Lowering(_) | Refusal::Corpus(_))
                        | Maybe::Absent(_) => Vec::new(),
                    };
                    (
                        declaration.name(),
                        declaration.span(),
                        declaration.stated().clone(),
                        declaration.owed(),
                        declaration.waits().to_vec(),
                        (core::mem::discriminant(&produced), verdict),
                        (declaration.outcome(), compared),
                    )
                })
                .collect()
        }

        let pbg = grammar();
        // The fold's nested calls and `told`'s are elaborated: the closure's
        // nodes are located before the document's lowering, the document's
        // after it.
        let closure_text = "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  P : (x : \
                            Int) --> Int;\n  rule S(P(x)) ==> x;\n  rule P(S(x)) ==> x;\n}\ndef \
                            rec tell(n : Int) -> -F Int {\n  case n {\n    Z => Z,\n    S(x) \
                            => S(tell[<](x)),\n    P(x) => P(tell[<](x))\n  }\n}\ndef one : \
                            Integer ;\ndef one = 1 ;\ndef owed : Integer ;\ndef lost = nowhere \
                            ;\ndef bad : Integer ;\ndef bad = \"bad\" ;\n";
        let first = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n@[ \
                     runs(\"1\") ] def ran = one ;\ndef told = S(tell(Z)) ;\n";
        let second = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = \"two\" \
                      ;\ndef three : Integer ;\ndef three = owed ;\n";
        let base = ByteOffset::from(closure_text.len());
        let unit = Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
        ])
        .expect("two sources make a unit");
        let mut lowerings = LoweringCount::default();
        let closure = Arc::new(
            lower_closure(
                Arc::new(grammar()),
                String::from(closure_text),
                Unit::new(vec![UnitSource::new(ByteOffset::from(0_usize), Vec::new())])
                    .expect("one source makes a unit"),
                &mut lowerings,
            )
            .expect("the closure is held"),
        );
        let held = JudgedClosure::new(
            Arc::clone(&closure),
            &HostGrant::UNBOUNDED,
            CorpusRoot::Strict,
        )
        .expect("the closure lowers to its end");
        for (step, own) in [first, second, first].into_iter().enumerate() {
            let text = format!("{closure_text}{own}");
            let text = SourceText::from(text.as_str());
            let parsed = || {
                parse(&pbg, SourceText::from(own))
                    .expect("the document parses")
                    .after(closure.tree(), text)
                    .expect("the document lays after its closure")
            };
            let judged = after(
                &held,
                (SourceText::from(own), text),
                (&unit, base),
                &mut lowerings,
            );
            assert_eq!(
                lowerings,
                LoweringCount::from(step.saturating_add(2_usize)),
                "each document counts its own source"
            );
            let Ok(Composed::Settled { ref origins, .. }) = judged.settled
            else {
                panic!("the document settles");
            };
            let carried = &held.judgement().elaborated.0;
            assert!(!carried.is_empty(), "the closure's fold is elaborated");
            for &pair in carried {
                let (source, minted) = match pair {
                    Carried::Value(source, minted) => {
                        (origins.value(source), origins.value(minted))
                    },
                    Carried::Computation(source, minted) => {
                        (origins.computation(source), origins.computation(minted))
                    },
                    Carried::ValueType(source, minted) => {
                        (origins.value_type(source), origins.value_type(minted))
                    },
                    Carried::CompType(source, minted) => {
                        (origins.comp_type(source), origins.comp_type(minted))
                    },
                };
                assert!(
                    matches!(source, Maybe::Absent(_)) || matches!(minted, Maybe::Present(_)),
                    "revision {step} locates {pair:?}, which the closure's fold minted"
                );
            }
            let fresh_closure = JudgedClosure::new(
                Arc::clone(&closure),
                &HostGrant::UNBOUNDED,
                CorpusRoot::Strict,
            )
            .expect("the closure lowers to its end");
            let fresh = after(
                &fresh_closure,
                (SourceText::from(own), text),
                (&unit, base),
                &mut LoweringCount::default(),
            );
            assert_eq!(
                judged.settled, fresh.settled,
                "revision {step} composes as on a fresh judgement of its closure"
            );
            let kernel = judged
                .admission
                .clone()
                .admit()
                .expect("the kernel readmits the document");
            assert_eq!(
                kernel,
                fresh.admission.admit().expect("and the fresh one"),
                "to one artifact"
            );
            let (whole_module, whole_arena) = module(
                lower_parsed_unit(
                    &pbg,
                    parsed(),
                    &unit,
                    &mut LoweringCount::default(),
                    &mut gandr_surface_lowering::coincide::Decisions::none(),
                )
                .expect("the whole unit lowers"),
            );
            let whole = judge_member(
                CorpusRoot::Strict,
                (whole_module, text),
                whole_arena,
                &HostGrant::UNBOUNDED,
                base,
            );
            assert_eq!(
                reported(judged),
                reported(whole),
                "revision {step} reports what the whole unit reports"
            );
        }
    }

    /// A readmission that resumes nothing and records nothing.
    const WHOLE: (
        bridge::LeadingCount,
        Maybe<&bridge::Crossed, bridge::crossed::Absent>,
    ) = (
        bridge::LeadingCount::NONE,
        Maybe::Absent(bridge::crossed::Absent::Unasked),
    );

    /// `source` composed under `root`, which must settle.
    ///
    /// # Specification
    /// - requires: the grammar admits the named fixture declarations and their
    ///   source composes to a module without an engine fault.
    /// - ensures: returns that module's report; every reported name occurs in
    ///   the supplied source.
    /// - fails: never.
    /// - panics: if composition faults or refuses the source as a whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literal names, outcomes and ledger counts in a mixed
    ///   fixture separate lost declarations and wrong root policies. The
    ///   witnesses use explicit simple names, not every naming form or failure.
    /// - witness: `compose::tests::a_module_settles_every_declaration_once`
    /// - witness: `compose::tests::the_root_decides_what_an_expectation_means`
    #[spec(ensures: |ref ret| ret.declarations().iter()
        .all(|declaration| source.as_ref().contains(declaration.name().as_ref())))]
    fn settled<'source>(
        grammar: &Pbg,
        root: CorpusRoot,
        source: SourceText<'source>,
    ) -> gandr_surface_corpus::SettleReport<'source>
    {
        let mut lowerings = LoweringCount::default();
        match compose(grammar, root, source, &mut lowerings) {
            Ok(Composed::Settled { report, .. }) => report,
            Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            Err(fault) => panic!("faulted: {fault}"),
        }
    }

    #[test]
    fn a_module_settles_every_declaration_once()
    {
        let grammar = grammar();
        let report = settled(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"def answer : Integer ;
def answer = 42 ;
def copy = answer ;
@[ owes(1) ] def later : Integer ;
@[ refuses("UnresolvedName") ] def broken = missing ;
def wrong : Integer ;
def wrong = "text" ;"#,
            ),
        );
        let rows: Vec<(String, Settlement, Outcome)> = report
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    declaration.name().to_string(),
                    declaration.settlement(),
                    declaration.outcome(),
                )
            })
            .collect();
        let checks = |owed: usize| Outcome::Checks(gandr_core_checker::ObligationCount::from(owed));
        assert_eq!(
            rows,
            vec![
                ("answer".to_owned(), Settlement::Settled, checks(0)),
                ("copy".to_owned(), Settlement::Settled, checks(0)),
                ("later".to_owned(), Settlement::Settled, checks(1)),
                (
                    "broken".to_owned(),
                    Settlement::Settled,
                    Outcome::Refuses(gandr_surface_corpus::RefusalName::UnresolvedName)
                ),
                (
                    "wrong".to_owned(),
                    Settlement::Unsettled,
                    Outcome::Refuses(gandr_surface_corpus::RefusalName::TypeMismatch)
                ),
            ],
            "one report per declared name, in admission order"
        );
        assert!(
            matches!(
                report.declarations()[0].produced(),
                Produced::Judged(Verdict::Checked { .. })
            ),
            "a signed body checks"
        );
        assert!(
            matches!(
                report.declarations()[1].produced(),
                Produced::Judged(Verdict::Synthesised { .. })
            ),
            "an unsigned body synthesises"
        );
        assert_eq!(
            usize::from(report.ledger()),
            1_usize,
            "the owed signature is the module's one obligation"
        );
    }

    #[test]
    fn a_host_entry_names_the_worlds_a_module_declares()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "world operator ;\nworld seat ;\ndef moved() -> -F Integer { migrate [seat] { pure 1 \
             } }\n",
        );
        let moved = |grant: &HostGrant| {
            let Lowered::Module { module, arena } =
                lower_source(&grammar, source, &mut LoweringCount::default())
                    .expect("the module lowers")
                    .into_lowered()
            else {
                panic!("the module is not refused whole");
            };
            match judge_module(CorpusRoot::Fixture, (module, source), arena, grant) {
                Ok(Composed::Settled { report, .. }) => report
                    .declarations()
                    .last()
                    .map(gandr_surface_corpus::DeclarationReport::outcome),
                Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
                Err(fault) => panic!("faulted: {fault}"),
            }
        };
        let [operator, seat, elsewhere] = ["operator", "seat", "elsewhere"].map(WorldName::from);
        assert_eq!(
            moved(&HostGrant::UNBOUNDED),
            Some(Outcome::Refuses(RefusalName::CapabilityMissing)),
            "without an entry the migration holds no capability"
        );
        assert_eq!(
            moved(&HostGrant::UNBOUNDED.entering(vec![operator.clone(), seat])),
            Some(Outcome::Checks(ObligationCount::from(0_usize))),
            "the host's entry at the operator holds one capability to the seat"
        );
        assert_eq!(
            moved(&HostGrant::UNBOUNDED.entering(vec![operator, elsewhere])),
            Some(Outcome::Refuses(RefusalName::HostWorldUndeclared)),
            "a world the module declares nowhere grants nothing"
        );
    }

    #[test]
    fn an_effectful_declaration_stays_on_the_checkers_side()
    {
        let grammar = grammar();
        let report = settled(
            &grammar,
            CorpusRoot::Strict,
            SourceText::from(concat!(
                "def peek(c : Cap {read}) -> -F [Fs] String { c.read(\"notes\") }\n",
                "def quit() -> -F Unit { handle c : Proc { c.exit(1) } with { pure(x) => pure x, oper exit(code, k) => k(unit) } }\n",
                "def answer : Integer ;\n",
                "def answer = 42 ;\n",
            )),
        );
        let rows: Vec<(String, Settlement)> = report
            .declarations()
            .iter()
            .map(|declaration| (declaration.name().to_string(), declaration.settlement()))
            .collect();
        assert_eq!(
            rows,
            vec![
                ("peek".to_owned(), Settlement::Settled),
                ("quit".to_owned(), Settlement::Settled),
                ("answer".to_owned(), Settlement::Settled),
            ],
            "the kernel's refusal of an exercise and a scope is no disagreement, \
             and the pure declaration beside them is still readmitted"
        );
    }

    #[test]
    fn a_root_that_is_no_list_of_declarations_is_refused_whole()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let composed = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from("pure greeting"),
            &mut lowerings,
        );
        let Ok(Composed::Refused(refusal)) = composed
        else {
            panic!("a root of nothing but a top-level expression refuses the module");
        };
        assert!(
            matches!(refusal, LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            }),
            "a root child that is no declaration is out of the fragment: {refusal}"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::Unimplemented(gandr_core_term::TrackingIssue::RUN_TARGET),
            "a root expression is a run target, which is not implemented yet"
        );
    }

    #[test]
    fn each_composition_lowers_once()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let sources = [
            "def a = 3 ;",
            "pure 3",
            r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
        ];
        for (composed, source) in sources.into_iter().enumerate() {
            let result = compose(
                &grammar,
                CorpusRoot::Fixture,
                SourceText::from(source),
                &mut lowerings,
            );
            assert!(result.is_ok(), "{source} composes");
            assert_eq!(
                usize::from(lowerings),
                composed.saturating_add(1_usize),
                "each composition lowers exactly once"
            );
        }
    }

    #[test]
    fn a_lowering_carries_the_parse_obligations()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        for (source, refused, expected) in [
            (
                "def bad = 1 ~ 2 ;\ndef good = 2 ;",
                false,
                &[(gandr_surface_parser::Oblig::UnmoldedTok, 12_usize, 13_usize)][..],
            ),
            ("def good = 2 ;", false, &[][..]),
            (
                "def bad = 1 ~ 2 ;\npure 3",
                false,
                &[(gandr_surface_parser::Oblig::UnmoldedTok, 12_usize, 13_usize)][..],
            ),
            (
                "pure 1 ~ 2",
                true,
                &[(gandr_surface_parser::Oblig::UnmoldedTok, 7_usize, 8_usize)][..],
            ),
        ] {
            let lowering = lower_source(&grammar, SourceText::from(source), &mut lowerings)
                .expect("lowers without a fault");
            let repairs = lowering.obligations().iter().map(|repair| {
                (
                    repair.class,
                    usize::from(repair.span.start()),
                    usize::from(repair.span.end()),
                )
            });
            assert!(
                repairs.eq(expected.iter().copied()),
                "the unexpected token keeps its repair class and exact byte span for {source:?}"
            );
            assert_eq!(
                matches!(lowering.into_lowered(), Lowered::Refused(_)),
                refused,
                "{source:?} is read as a module or refused whole"
            );
        }
        assert_eq!(
            usize::from(lowerings),
            4_usize,
            "each lowering is counted once"
        );
    }

    #[test]
    fn the_root_decides_what_an_expectation_means()
    {
        let grammar = grammar();
        let source = SourceText::from(r#"@[ owes(1) ] def later : Integer ;"#);
        let fixture = settled(&grammar, CorpusRoot::Fixture, source);
        let strict = settled(&grammar, CorpusRoot::Strict, source);
        assert_eq!(
            fixture.declarations()[0].settlement(),
            Settlement::Settled,
            "the fixture root reads the expectation"
        );
        assert_eq!(
            strict.declarations()[0].settlement(),
            Settlement::Unsettled,
            "the strict root refuses it"
        );
        assert_eq!(
            strict.declarations()[0].outcome(),
            Outcome::Refuses(gandr_surface_corpus::RefusalName::ExpectationOutsideFixtureRoot),
            "the guard stands in for what the declaration produced"
        );
    }

    #[test]
    fn a_refusal_at_a_declaration_form_is_unstatable()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let composed = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"@[ refuses("ImplicitTelescope") ] def f @[a : Type] = 1 ;
@[ refuses("UnresolvedName") ] def g = missing ;
def h = 1 ;"#,
            ),
            &mut lowerings,
        );
        let Ok(Composed::Settled {
            report, unstatable, ..
        }) = composed
        else {
            panic!("the module lowers");
        };
        assert!(
            matches!(unstatable.as_slice(), [
                LoweringRefusal::ImplicitTelescope { .. }
            ]),
            "the implicit telescope is refused at its own form, and only it"
        );
        let settlements: Vec<Settlement> = report
            .declarations()
            .iter()
            .map(gandr_surface_corpus::DeclarationReport::settlement)
            .collect();
        assert_eq!(
            settlements,
            vec![
                Settlement::Unsettled,
                Settlement::Settled,
                Settlement::Settled
            ],
            "the refused form's expectation cannot be read; a refused body's can"
        );
    }

    #[test]
    fn a_tail_without_a_result_type_lowers_unsigned()
    {
        let grammar = grammar();
        let source = SourceText::from("def f(x: Integer) { return x }");
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        assert!(
            matches!(
                module.declarations()[0].outcome(),
                DeclarationOutcome::Bodied { .. }
            ),
            "the lowering writes the body alone and refuses nothing"
        );
        assert_eq!(
            settled(&grammar, CorpusRoot::Fixture, source).declarations()[0].outcome(),
            Outcome::Refuses(RefusalName::NotSynthesisable),
            "the checker, not the lowering, refuses the body it cannot type"
        );
    }

    #[test]
    fn a_kernel_disagreement_is_an_engine_fault()
    {
        let grammar = grammar();
        let source = SourceText::from(
            r#"def w : Integer ; def w = "text" ; def r = w ; def a : Integer ; def a = 1 ;"#,
        );
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &adapt(&module),
        );
        let admission = readmitted(&mut arena, &verdicts, WHOLE, &Unretired)
            .whole()
            .0
            .expect("marks and withheld references are not disagreements");
        let [ref marked, ref withheld, ref defined] = *admission.readmitted()
        else {
            panic!("each declaration has one readmission outcome");
        };
        assert!(matches!(
            (marked.outcome(), withheld.outcome(), defined.outcome()),
            (
                &bridge::Outcome::Marked(_),
                &bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
                &bridge::Outcome::Defined { .. }
            ),
        ));

        assert!(
            matches!(verdicts.judged()[1].verdict(), Verdict::Synthesised { .. }),
            "the reference is accepted by the checker despite the withheld body"
        );
        let mut foreign = CoreArena::new();
        let (Err(fault), _) = readmitted(&mut foreign, &verdicts, WHOLE, &Unretired).whole()
        else {
            panic!("over a foreign arena the accepted ids dangle");
        };
        assert_eq!(
            fault.constant(),
            module.declarations()[1].constant(),
            "the first accepted declaration is the one reported"
        );
        assert!(
            matches!(
                fault.outcome(),
                bridge::Outcome::Refused(bridge::Refusal::DanglingNode { .. })
            ),
            "the bridge refused its dangling ids"
        );
        let rendered = crate::SourceFault::Compose(ComposeFault::Readmission(fault)).to_string();
        let positions = rendered
            .split(|character: char| !character.is_ascii_digit())
            .filter(|part| !part.is_empty())
            .map(|part| part.parse::<usize>().expect("the position is decimal"));
        assert!(
            positions.eq([1_usize]),
            "the fault retains its nonzero position"
        );
    }

    #[test]
    fn a_judged_module_renders_before_its_admission()
    {
        // The second module applies a static operator at three instances, so
        // its readmission mints their reducts into the arena.
        let sources = [
            r#"def a : Integer ; def a = 1 ; @[ owes(1) ] def later : Integer ; def w : Integer ; def w = "text" ; def r = w ;"#,
            include_str!("../../surface-corpus/strict/classifier/relative-monad.gandr"),
        ];
        let grammar = grammar();
        for source in sources {
            let mut lowerings = LoweringCount::default();
            let lower = |lowerings: &mut LoweringCount| {
                let Lowered::Module { module, arena } =
                    lower_source(&grammar, SourceText::from(source), lowerings)
                        .expect("the module lowers")
                        .into_lowered()
                else {
                    panic!("the module is not refused whole");
                };
                (module, arena)
            };
            // The order the composition ran before: readmit, then settle.
            let (mut module, mut arena) = lower(&mut lowerings);
            let verdicts = check_module(
                &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
                &adapt(&module),
            );
            let readmission = readmitted(&mut arena, &verdicts, WHOLE, &Unretired)
                .whole()
                .0
                .expect("the kernel re-derives every acceptance");
            let kernel = readmission.export(module.structured_names());
            let mut program = Program::new(&arena, &module, &verdicts);
            let report = settle(
                CorpusRoot::Fixture,
                &arena,
                &module,
                &verdicts,
                &mut program,
            )
            .expect("the verdicts settle");
            let exercised = Exercised::of(&arena, &module, &report);
            let unstatable = super::unstatable(&module);
            let failures = super::Failures::of(&verdicts);
            super::located(
                module.origins_mut(),
                &verdicts,
                super::ConstantIndex::from(0_usize),
            );
            let spellings = super::TypeSpellings::of(
                &arena,
                &module,
                &report,
                &failures,
                (module.origins(), SourceText::from(source)),
            );
            let shadowed = module.recognition().shadowed().to_vec();
            let inferred = module.inferred_exits().to_vec();
            let runs = super::inferred_runs(&module, &verdicts);
            let deprecated = module.deprecated_uses(&arena);
            let unused = super::unused_binders(&arena, &module, &report, |_| true);
            let readmitted_first = Composed::Settled {
                report,
                exercised,
                unstatable,
                origins: module.into_origins(),
                spellings,
                failures,
                shadowed,
                inferred,
                runs,
                deprecated,
                unused,
                unreached: Vec::new(),
                kernel: Maybe::Present(kernel),
                program,
            };
            let (module, arena) = lower(&mut lowerings);
            let judged = judge(
                CorpusRoot::Fixture,
                (module, SourceText::from(source)),
                arena,
                &HostGrant::UNBOUNDED,
            );
            let Ok(
                ref settled @ Composed::Settled {
                    kernel: Maybe::Absent(admitted::Absent::Pending),
                    ..
                },
            ) = *judged.settled()
            else {
                panic!("the module settles before its admission");
            };
            let Composed::Settled {
                kernel: Maybe::Present(ref kernel),
                ..
            } = readmitted_first
            else {
                panic!("the module settles after its readmission");
            };
            assert_eq!(
                settled.clone().admitted(kernel.clone()),
                readmitted_first,
                "settling before the readmission reads what settling after it read"
            );
            assert!(
                judged
                    .admit()
                    .is_ok_and(|admitted| admitted == readmitted_first),
                "the admission completes the composition with the same kernel artifact"
            );
        }
    }

    /// #776: an admission resumed from the record another revision's
    /// admission made of the declarations both lead with exports, byte for
    /// byte, what a whole admission of the revision exports, crossing only the
    /// revision's own declarations.
    #[test]
    fn a_resumed_admission_exports_what_a_whole_one_does_776()
    {
        let grammar = grammar();
        let closure = "def one : Integer ; def one = 1 ;\ndef two : Integer ; def two = one ;\n";
        let first = format!("{closure}def three : Integer ; def three = two ;");
        let later = format!(
            "{closure}def four : Integer ; def four = 4 ;\ndef five : Integer ; def five = two ;"
        );
        let admission = |text: &str| {
            let Lowered::Module { module, arena } = lower_source(
                &grammar,
                SourceText::from(text),
                &mut LoweringCount::default(),
            )
            .expect("the revision lowers")
            .into_lowered()
            else {
                panic!("the revision is not refused whole");
            };
            judge(
                CorpusRoot::Fixture,
                (module, SourceText::from(text)),
                arena,
                &HostGrant::UNBOUNDED,
            )
            .into_parts()
            .1
        };
        let recorded = admission(&first).admit_resuming(
            bridge::LeadingCount::from(2_usize),
            Maybe::Absent(bridge::crossed::Absent::Unasked),
        );
        assert!(recorded.artifact.is_ok(), "{:?}", recorded.artifact);
        assert_eq!(
            usize::from(recorded.resumed),
            0_usize,
            "nothing was held to resume"
        );
        let Maybe::Present(ref crossed) = recorded.crossed
        else {
            panic!("the closure is recorded: {:?}", recorded.crossed);
        };
        let whole = admission(&later).admit();
        let resumed = admission(&later)
            .admit_resuming(bridge::LeadingCount::from(2_usize), Maybe::Present(crossed));
        assert_eq!(
            (usize::from(resumed.resumed), usize::from(resumed.judged)),
            (2_usize, 4_usize),
            "the closure's two declarations are resumed, and the revision's own two cross"
        );
        assert_eq!(
            resumed.artifact, whole,
            "the resumed artifact is the whole one, byte for byte"
        );
    }

    /// A poll that answers wanted a number of times, then retired.
    #[repr(transparent)]
    struct After(core::cell::Cell<usize>);

    impl Retirement for After
    {
        type Retired = ();

        /// Wanted while polls are left, then retired.
        ///
        /// # Specification
        /// trivial.
        fn demand(&self) -> Demand<()>
        {
            self.0
                .get()
                .checked_sub(1_usize)
                .map_or(Demand::Retired(()), |left| {
                    self.0.set(left);
                    Demand::Wanted
                })
        }
    }

    /// #1547: an admission retired before its third declaration answers the
    /// record of the two it crossed, and an admission resumed from that record
    /// exports, byte for byte, what a whole admission exports, crossing only
    /// the third.
    #[test]
    fn a_retired_admission_resumes_from_its_record_1547()
    {
        let grammar = grammar();
        let text = "def one : Integer ; def one = 1 ;\ndef two : Integer ; def two = one ;\ndef three : Integer ; def three = two ;";
        let admission = || {
            let Lowered::Module { module, arena } = lower_source(
                &grammar,
                SourceText::from(text),
                &mut LoweringCount::default(),
            )
            .expect("the revision lowers")
            .into_lowered()
            else {
                panic!("the revision is not refused whole");
            };
            judge(
                CorpusRoot::Fixture,
                (module, SourceText::from(text)),
                arena,
                &HostGrant::UNBOUNDED,
            )
            .into_parts()
            .1
        };
        let Polled::Retired((), Maybe::Present(record)) = admission().admit_retiring(
            bridge::LeadingCount::from(3_usize),
            Maybe::Absent(bridge::crossed::Absent::Unasked),
            &After(core::cell::Cell::new(2_usize)),
        )
        else {
            panic!("the admission is retired before its third declaration with a record");
        };
        assert_eq!(
            usize::from(record.boundary()),
            2_usize,
            "the record holds the two declarations crossed before the retirement"
        );
        let whole = admission().admit();
        let resumed = admission()
            .admit_retiring(
                bridge::LeadingCount::from(3_usize),
                Maybe::Present(&record),
                &Unretired,
            )
            .whole();
        assert_eq!(
            (usize::from(resumed.resumed), usize::from(resumed.judged)),
            (2_usize, 3_usize),
            "the two crossed before the retirement are resumed, and the third crosses"
        );
        assert_eq!(
            resumed.artifact, whole,
            "the resumed artifact is the whole one, byte for byte"
        );
    }

    #[test]
    fn the_kernel_artifact_holds_what_crossed_under_its_names()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let Ok(Composed::Settled {
            kernel: Maybe::Present(kernel),
            ..
        }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"def a : Integer ; def a = 1 ; @[ owes(1) ] def later : Integer ; def w : Integer ; def w = "text" ; def r = w ;"#,
            ),
            &mut lowerings,
        )
        else {
            panic!("the module settles");
        };
        let decoded = decode(kernel.as_image()).expect("the kernel's own export decodes");
        let names: Vec<Vec<&str>> = decoded
            .declarations()
            .iter()
            .map(|marked| {
                marked
                    .declaration()
                    .name()
                    .segments()
                    .iter()
                    .map(AsRef::as_ref)
                    .collect()
            })
            .collect();
        assert_eq!(
            vec![vec!["a"], vec!["later"]],
            names,
            "the definition and the owed axiom cross under their names; the refused declaration \
             and the one withheld for naming it do not"
        );
    }

    #[test]
    fn a_sealed_module_settles_its_abstract_type()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let Ok(Composed::Settled {
            report,
            kernel: Maybe::Present(kernel),
            ..
        }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                "module Counter :> #{ type T, seed : T } { type T = Integer ; def seed = 7 ; }\n\
                 def held : Counter.T ;\n\
                 def held = Counter.seed ;\n\
                 def leak : Integer ;\n\
                 def leak = Counter.seed ;",
            ),
            &mut lowerings,
        )
        else {
            panic!("the sealed module settles and crosses");
        };
        let rows: Vec<(String, Settlement, Outcome)> = report
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    declaration.name().to_string(),
                    declaration.settlement(),
                    declaration.outcome(),
                )
            })
            .collect();
        let checks = || Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
        assert_eq!(
            rows,
            vec![
                ("T".to_owned(), Settlement::Settled, checks()),
                ("seed".to_owned(), Settlement::Settled, checks()),
                ("held".to_owned(), Settlement::Settled, checks()),
                (
                    "leak".to_owned(),
                    Settlement::Unsettled,
                    Outcome::Refuses(RefusalName::TypeMismatch)
                ),
            ],
            "the abstract type is admitted first, the member checks at its representation, a \
             client at the atom, and the atom is not its representation outside"
        );
        assert!(
            matches!(
                report.declarations()[0].produced(),
                Produced::Judged(Verdict::Data)
            ),
            "the abstract type is judged as a type former, with no axiom behind it"
        );
        let decoded = decode(kernel.as_image()).expect("the kernel's own export decodes");
        let crossed: Vec<(Vec<&str>, bool)> = decoded
            .declarations()
            .iter()
            .map(|marked| {
                (
                    marked
                        .declaration()
                        .name()
                        .segments()
                        .iter()
                        .map(AsRef::as_ref)
                        .collect(),
                    matches!(
                        *marked.declaration().content(),
                        gandr_kernel_term::DeclarationContent::AbstractType { .. }
                    ),
                )
            })
            .collect();
        assert_eq!(
            crossed,
            vec![
                (vec!["Counter", "T"], true),
                (vec!["Counter", "seed"], false),
                (vec!["held"], false),
            ],
            "the atom crosses as the kernel's abstract type, ahead of the definitions that read \
             it; the leak does not cross"
        );
    }

    #[test]
    fn a_sealed_atom_s_identity_decides_what_its_relation_s_evidence_is()
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let sealed = |name: &str, identity: &str| {
            format!(
                "module {name} :> #{{ type T, origin : T, other : T }} {{ {identity} type T = \
                 Unit ; def origin = unit ; def other = unit ; }}\ndef evidence{name} : \
                 Path({name}.T, {name}.origin, {name}.other) ;\ndef evidence{name} = unit ;\n"
            )
        };
        let source = [
            "def related(a : Unit, b : Unit) -> -F Type { return Unit }\n".to_owned(),
            "def reflexive(a : Unit) -> -F related(a, a) { return unit }\n".to_owned(),
            "def contraction(a : Unit, b : Unit, r : related(a, b)) -> -F Path(#{ y : Unit, s : \
             related(a, y) }, (b, r), (a, reflexive(a))) { return (unit, unit) }\n"
                .to_owned(),
            sealed("Lawful", "@[ identity((related, reflexive, contraction)) ]"),
            sealed("Lawless", "@[ identity((related, reflexive)) ]"),
            sealed("Bare", ""),
        ]
        .concat();
        let Ok(Composed::Settled { report, .. }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(source.as_str()),
            &mut lowerings,
        )
        else {
            panic!("the three sealed modules settle");
        };
        let mut evidence: Vec<(String, Outcome)> = report
            .declarations()
            .iter()
            .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
            .collect();
        evidence.retain(|&(ref name, _)| name.starts_with("evidence"));
        assert_eq!(
            evidence,
            vec![
                (
                    "evidenceLawful".to_owned(),
                    Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize))
                ),
                (
                    "evidenceLawless".to_owned(),
                    Outcome::Refuses(RefusalName::AtomTransport)
                ),
                (
                    "evidenceBare".to_owned(),
                    Outcome::Refuses(RefusalName::TypeMismatch)
                ),
            ],
            "the relation's evidence is a path at a lawful atom, refused by name at an atom \
             stating no law, and no path at an atom stating no identity"
        );
    }

    #[test]
    fn form_refusals_retain_admission_order()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "def first @[a : Type] = 1 ;\n\
             def broken = missing ;\n\
             def value = 3 ;\n\
             def last @[a : Type] = 1 ;",
        );
        let mut lowerings = LoweringCount::default();
        let Lowered::Module { module, .. } = lower_source(&grammar, source, &mut lowerings)
            .expect("the mixed module lowers")
            .into_lowered()
        else {
            panic!("individual forms do not refuse the whole source");
        };
        let [ref first, _, _, ref last] = *module.declarations()
        else {
            panic!("the four declarations retain their admission positions");
        };
        let (DeclarationOutcome::Refused(first), DeclarationOutcome::Refused(last)) =
            (first.outcome(), last.outcome())
        else {
            panic!("the implicit telescopes are outside the fragment");
        };
        assert_ne!(
            first, last,
            "the two refused forms have distinct source spans"
        );
        assert_eq!(super::unstatable(&module).as_slice(), &[first, last]);
    }

    #[test]
    fn a_body_prints_with_its_exits_elided_and_reads_back_to_its_term()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "def kept(n : Integer) -> -F Integer { return n }\n\
             def kept_elided(n : Integer) -> -F Integer { n }\n\
             def kept_printed : +U (Integer -> -F Integer) ;\n\
             def kept_printed = thunk { fn (a) { a } } ;\n\
             def called(n : Integer) -> -F Integer { become kept(n) }\n\
             def called_elided(n : Integer) -> -F Integer { kept(n) }\n\
             def called_printed : +U (Integer -> -F Integer) ;\n\
             def called_printed = thunk { fn (a) { kept(a) } } ;\n\
             def sequenced(n : Integer) -> -F Integer { run m <- kept(n) ; become kept(m) }\n\
             def sequenced_elided(n : Integer) -> -F Integer { run m <- kept(n) ; kept(m) }\n\
             def sequenced_printed : +U (Integer -> -F Integer) ;\n\
             def sequenced_printed = thunk { fn (a) { run b <- kept(a) ; kept(b) } } ;\n\
             def suspended(n : Integer) -> -F (+U (-F Integer)) { return thunk { become kept(n) } }\n\
             def suspended_elided(n : Integer) -> -F (+U (-F Integer)) { thunk { kept(n) } }\n\
             def suspended_printed : +U (Integer -> -F (+U (-F Integer))) ;\n\
             def suspended_printed = thunk { fn (a) { thunk { kept(a) } } } ;\n",
        );
        let mut lowerings = LoweringCount::default();
        let Lowered::Module { module, arena } = lower_source(&grammar, source, &mut lowerings)
            .expect("the module lowers")
            .into_lowered()
        else {
            panic!("the module is read");
        };
        let spelled = constant_names(&module);
        let names: Vec<Name<'_>> = spelled
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let printer = CoreSource::new(&arena, &names);
        let body = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            match declaration.outcome() {
                DeclarationOutcome::Completed { body, .. }
                | DeclarationOutcome::Bodied { body } => body,
                other @ (DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_)) => {
                    panic!("`{wanted}` lowers a body, not {other:?}")
                },
            }
        };
        let printed = |wanted: &str| {
            let Some(&Value::Thunk(computation)) = arena.value(body(wanted))
            else {
                panic!("`{wanted}` is a suspended function");
            };
            let presentation = present_computation(
                &printer,
                CoreNode::Computation(computation),
                PageWidth::from(100_u32),
                Form::Explicit.into(),
            )
            .expect("the body lays out");
            (presentation.to_string(), presentation.fidelity())
        };
        for (written, expected) in [
            ("kept", "fn (a) { a }"),
            ("called", "fn (a) { kept(a) }"),
            ("sequenced", "fn (a) { run b <- kept(a) ; kept(b) }"),
            ("suspended", "fn (a) { thunk { kept(a) } }"),
        ] {
            let (elided, restated) = (format!("{written}_elided"), format!("{written}_printed"));
            for name in [written, elided.as_str(), restated.as_str()] {
                assert_eq!(
                    printed(name),
                    (String::from(expected), Fidelity::Faithful),
                    "`{name}` prints in the canonical form, its exits elided"
                );
            }
            assert_eq!(
                equal_certificate_syntax(&arena, body(written), body(&restated)),
                CertificateEquality::Equal,
                "`{written}`'s printed body reads back to its term"
            );
        }
    }

    #[test]
    fn the_sugared_form_reads_back_to_the_term_it_prints()
    {
        let types = [
            ("+U (-F Integer)", "() => Integer"),
            ("+U (Integer -> -F String)", "Integer => String"),
            (
                "+U (Integer -> String -> -F Unit)",
                "(Integer, String) => Unit",
            ),
            (
                "+U (+U (Integer -> -F Integer) -> -F Integer)",
                "(Integer => Integer) => Integer",
            ),
            (
                "+U (Integer -> -F (+U (-F Integer)))",
                "Integer => () => Integer",
            ),
            ("#{Integer, String, Unit}", "Integer * String * Unit"),
            ("#{#{Integer, String}, Unit}", "(Integer * String) * Unit"),
            ("+{Integer, +{String, Unit}}", "Integer + (String + Unit)"),
            ("+{#{Integer, String}, Unit}", "Integer * String + Unit"),
            ("#{+{Integer, String}, Unit}", "(Integer + String) * Unit"),
            (
                "+U (&{-F Integer, &{-F Unit, -F String}})",
                "+U (-F Integer & (-F Unit & -F String))",
            ),
            (
                "+U (&{-F Integer, -F Unit, -F String})",
                "+U (-F Integer & -F Unit & -F String)",
            ),
            (
                "+U (&{&{-F Integer, -F Unit}, -F String})",
                "+U ((-F Integer & -F Unit) & -F String)",
            ),
            (
                "+U (#{Integer, String} -> -F +{Integer, Unit})",
                "Integer * String => Integer + Unit",
            ),
        ];
        let mut written = types
            .iter()
            .enumerate()
            .map(|(index, &(explicit, sugared))| {
                format!("def e{index} : {explicit} ;\ndef s{index} : {sugared} ;\n")
            })
            .collect::<Vec<String>>()
            .concat();
        written.push_str(
            "def pair : Integer * String ;\ndef pair = #{1, \"a\"} ;\n\
             def pair_sugared : Integer * String ;\ndef pair_sugared = (1, \"a\") ;\n\
             def pure_pair : () => Integer * String ;\n\
             def pure_pair = thunk { return #{1, \"a\"} } ;\n\
             def pure_pair_sugared : () => Integer * String ;\n\
             def pure_pair_sugared = thunk { pure (1, \"a\") } ;\n",
        );
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let Lowered::Module { module, arena } =
            lower_source(&grammar, SourceText::from(written.as_str()), &mut lowerings)
                .expect("the module lowers")
                .into_lowered()
        else {
            panic!("the module is read");
        };
        let spelled = constant_names(&module);
        let names: Vec<Name<'_>> = spelled
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let printer = CoreSource::new(&arena, &names);
        let outcome = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"))
                .outcome()
        };
        let declared = |wanted: &str| match outcome(wanted) {
            DeclarationOutcome::Completed { declared_type, .. }
            | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
            other @ (DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_)) => {
                panic!("`{wanted}` lowers a signature, not {other:?}")
            },
        };
        let body = |wanted: &str| match outcome(wanted) {
            DeclarationOutcome::Completed { body, .. } => body,
            other @ (DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_)) => panic!("`{wanted}` lowers a body, not {other:?}"),
        };
        let shown = |presented: Result<_, _>| {
            let presentation: gandr_surface_pretty::Presentation =
                presented.expect("the node lays out");
            (presentation.to_string(), presentation.fidelity())
        };
        for (index, &(explicit, sugared)) in types.iter().enumerate() {
            let (explicit_name, sugared_name) = (format!("e{index}"), format!("s{index}"));
            for name in [explicit_name.as_str(), sugared_name.as_str()] {
                assert_eq!(
                    shown(present_type(
                        &printer,
                        CoreNode::ValueType(declared(name)),
                        PageWidth::from(100_u32),
                        Form::Sugared.into(),
                    )),
                    (String::from(sugared), Fidelity::Faithful),
                    "`{explicit}` prints sugared as `{sugared}`"
                );
            }
            assert_eq!(
                equal_type_syntax(&arena, declared(&explicit_name), declared(&sugared_name)),
                CertificateEquality::Equal,
                "`{sugared}` reads back to `{explicit}`"
            );
        }
        let suspended = match arena.value(body("pure_pair")) {
            Some(&Value::Thunk(computation)) => computation,
            other => panic!("`pure_pair` is a suspended computation, not {other:?}"),
        };
        for (name, expected, presented) in [
            (
                "pair",
                "(1, \"a\")",
                present_value(
                    &printer,
                    CoreNode::Value(body("pair")),
                    PageWidth::from(100_u32),
                    Form::Sugared.into(),
                ),
            ),
            (
                "pure_pair",
                "(1, \"a\")",
                present_computation(
                    &printer,
                    CoreNode::Computation(suspended),
                    PageWidth::from(100_u32),
                    Form::Sugared.into(),
                ),
            ),
        ] {
            assert_eq!(
                shown(presented),
                (String::from(expected), Fidelity::Faithful),
                "`{name}` prints its tuple sugared"
            );
            let sugared = format!("{name}_sugared");
            assert_eq!(
                equal_certificate_syntax(&arena, body(name), body(&sugared)),
                CertificateEquality::Equal,
                "the sugared tuple of `{name}` reads back to its term"
            );
        }
    }

    #[test]
    fn a_body_prints_with_its_runs_elided_and_reads_back_to_its_elaboration()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "def kept(n : Integer) -> -F Integer { n }\n\
             def bound(n : Integer) -> -F Integer { run m <- kept(n) ; kept(m) }\n\
             def nested(n : Integer) -> -F Integer { kept(kept(n)) }\n\
             def nested_printed : +U (Integer -> -F Integer) ;\n\
             def nested_printed = thunk { fn (a) { kept(kept(a)) } } ;\n\
             def written(n : Integer) -> -F Integer { kept(run kept(n)) }\n\
             def written_printed : +U (Integer -> -F Integer) ;\n\
             def written_printed = thunk { fn (a) { kept(run kept(a)) } } ;\n",
        );
        let mut lowerings = LoweringCount::default();
        let Lowered::Module { module, mut arena } = lower_source(&grammar, source, &mut lowerings)
            .expect("the module lowers")
            .into_lowered()
        else {
            panic!("the module is read");
        };
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &adapt(&module),
        );
        let spelled = constant_names(&module);
        let names: Vec<Name<'_>> = spelled
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let constant = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"))
                .constant()
        };
        let defined = |wanted: &str| {
            *verdicts
                .definitions()
                .get(&constant(wanted))
                .unwrap_or_else(|| panic!("`{wanted}` checks"))
        };
        let printed = |wanted: &str| {
            let restoration = verdicts
                .nested_elaborations()
                .get(&constant(wanted))
                .map_or_else(Restoration::default, |elaboration| {
                    Restoration::of(elaboration.carried())
                });
            let Some(&Value::Thunk(computation)) = arena.value(defined(wanted))
            else {
                panic!("`{wanted}` is a suspended function");
            };
            let presentation = present_computation(
                &CoreSource::new(&arena, &names).restoring(&restoration),
                CoreNode::Computation(computation),
                PageWidth::from(100_u32),
                Form::Explicit.into(),
            )
            .expect("the body lays out");
            (presentation.to_string(), presentation.fidelity())
        };
        for (name, expected) in [
            ("bound", "fn (a) { run b <- kept(a) ; kept(b) }"),
            ("nested", "fn (a) { kept(kept(a)) }"),
            ("nested_printed", "fn (a) { kept(kept(a)) }"),
            ("written", "fn (a) { kept(run kept(a)) }"),
            ("written_printed", "fn (a) { kept(run kept(a)) }"),
        ] {
            assert_eq!(
                printed(name),
                (String::from(expected), Fidelity::Faithful),
                "`{name}` prints in the canonical form: an inferred run elided, a written one \
                 and a bind as written"
            );
        }
        for (left, right) in [
            ("nested", "bound"),
            ("nested", "nested_printed"),
            ("written", "bound"),
            ("written", "written_printed"),
        ] {
            assert_eq!(
                equal_certificate_syntax(&arena, defined(left), defined(right)),
                CertificateEquality::Equal,
                "`{left}` and `{right}` elaborate to one term"
            );
        }
    }

    #[test]
    fn a_nested_call_checks_to_the_certificate_of_its_bind()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "data Int : Type {\n\
             Z : Int;\n\
             S : (x : Int) --> Int;\n\
             P : (x : Int) --> Int;\n\
             rule S(P(x)) ==> x;\n\
             rule P(S(x)) ==> x;\n\
             }\n\
             def rec dbl(n : Int) -> -F Int {\n\
             case n { Z => Z, S(x) => S(S(dbl[<](x))), P(x) => P(P(dbl[<](x))) }\n\
             }\n\
             def rec bound(n : Int) -> -F Int {\n\
             case n {\n\
             Z => Z,\n\
             S(x) => { run d <- bound[<](x) ; S(S(d)) },\n\
             P(x) => { run d <- bound[<](x) ; P(P(d)) }\n\
             }\n\
             }\n",
        );
        let mut lowerings = LoweringCount::default();
        let Lowered::Module { module, mut arena } = lower_source(&grammar, source, &mut lowerings)
            .expect("the module lowers")
            .into_lowered()
        else {
            panic!("the module is read");
        };
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &adapt(&module),
        );
        let constant = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"))
                .constant()
        };
        let defined = |wanted: &str| {
            *verdicts
                .definitions()
                .get(&constant(wanted))
                .unwrap_or_else(|| panic!("`{wanted}` checks: {verdicts:?}"))
        };
        assert_eq!(
            equal_certificate_syntax(&arena, defined("dbl"), defined("bound")),
            CertificateEquality::Equal,
            "the nested call and its bind check to one term"
        );
        let spelled = constant_names(&module);
        let names: Vec<Name<'_>> = spelled
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let families = gandr_surface_diagnostics::Families::of(&module);
        let constructors = families.naming(&names);
        let restoration = verdicts
            .nested_elaborations()
            .get(&constant("dbl"))
            .map_or_else(Restoration::default, |elaboration| {
                Restoration::of(elaboration.carried())
            });
        // `rec dbl { fn (n) { case n { …, S(x) => arm, … } } }`: the arm at `S`.
        let arm = match arena.value(defined("dbl")) {
            Some(&Value::Thunk(fixpoint)) => match arena.computation(fixpoint) {
                Some(&Computation::Fixpoint { body, .. }) => match arena.computation(body) {
                    Some(&Computation::Lambda(case)) => match arena.computation(case) {
                        Some(&Computation::DataCase { ref branches, .. }) => {
                            branches.get(1_usize).copied()
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
        .expect("`dbl` is a fixpoint over a case with an arm at `S`");
        let context = [Some(Name::from("dbl")), Some(Name::from("n"))];
        let plain = CoreSource::new(&arena, &names)
            .naming(&constructors)
            .within(&context);
        for (source, expected) in [
            (plain.restoring(&restoration), "fn (a) { S(S(dbl(a))) }"),
            (plain, "fn (a) { run b <- dbl(a) ; S(S(b)) }"),
        ] {
            let presentation = present_computation(
                &source,
                CoreNode::Computation(arm),
                PageWidth::from(100_u32),
                Form::Sugared.into(),
            )
            .expect("the arm lays out");
            assert_eq!(
                (presentation.to_string(), presentation.fidelity()),
                (String::from(expected), Fidelity::Faithful),
                "restored, the bind prints as the nested call written; unrestored, as the bind"
            );
        }
    }

    #[test]
    fn each_binder_no_variable_reads_is_unused()
    {
        let grammar = grammar();
        let unused = |written: &str| {
            let mut lowerings = LoweringCount::default();
            let Ok(Composed::Settled { unused, .. }) = compose(
                &grammar,
                CorpusRoot::Fixture,
                SourceText::from(written),
                &mut lowerings,
            )
            else {
                panic!("the source composes");
            };
            unused
                .iter()
                .map(|span| {
                    let start = usize::from(span.start());
                    let line = written
                        .get(.. start)
                        .unwrap_or_default()
                        .matches('\n')
                        .count();
                    std::format!(
                        "{}:{}",
                        line.saturating_add(1),
                        written
                            .get(start .. usize::from(span.end()))
                            .unwrap_or_default()
                    )
                })
                .collect::<Vec<_>>()
        };
        let corpus = |file: &str| {
            std::fs::read_to_string(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../corpus")
                    .join(file),
            )
            .expect("the corpus source reads")
        };
        assert_eq!(
            unused(
                "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef pick(n : Nat, \
                 m : Nat) -> -F Nat {\n  run k <- pure Succ(n) ;\n  case n {\n    Zero => n,\n    \
                 Succ(p) => n\n  }\n}\ndef id : Nat => Nat ;\ndef id = thunk { fn (y) { Zero } } ;\n"
            ),
            ["5:m", "6:k", "9:p", "13:y"],
            "the unused parameter, `run` binder, pattern variable and lambda binder, the last in \
             the second half of a name declared in two; not the used parameter nor the \
             constructor's telescope binder"
        );
        assert_eq!(
            unused(
                "def chosen @[x : t] (t : Type) -> -F t { x }\ndef apply : (Type -> Type) -> Type \
                 -> Type ;\ndef apply = \\F. \\X. F(X) ;\n"
            ),
            [""; 0],
            "a binder read only in a type, or only by a static application, is used"
        );
        assert_eq!(
            unused(
                "def seat_left_open(n : Integer) -> -F Unit {\n  fork (seat : end) { pure unit } as \
                 desk;\n  close(desk)\n}\n"
            ),
            ["1:n"],
            "a fork's unused end is the checker's refusal and no lambda's or bind's, but the \
             refused declaration's unused parameter may be dropped (#1504)"
        );
        assert_eq!(
            unused(&corpus("pathological/control/capability-drop.gandr")),
            [""; 0],
            "an unused consumable capability is the checker's refusal, and its declaration \
             answers nothing"
        );
        assert_eq!(
            unused(&corpus("pathological/completion/buffer-misused.gandr")),
            ["26:first", "40:copied"],
            "each misused buffer is refused, yet a `run` binder no use reads may be dropped, \
             even one whose own head the checker refused (#1504)"
        );
        assert_eq!(
            unused(&corpus("surface/control-flow.gandr")),
            ["14:n"],
            "`tick` leaves its parameter unused; the capability `handled` handles is no lambda's \
             or bind's, and every other binder is used"
        );
    }

    /// A unit of one source, starting at the text's first byte.
    ///
    /// # Specification
    /// trivial.
    fn alone() -> gandr_surface_lowering::Unit
    {
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_syntax::ByteOffset;

        Unit::new(vec![UnitSource::new(ByteOffset::from(0_usize), Vec::new())])
            .expect("one source makes a unit")
    }

    /// A unit of two sources, the second starting at `base` and importing
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    fn pair(base: gandr_surface_syntax::ByteOffset) -> gandr_surface_lowering::Unit
    {
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_syntax::ByteOffset;

        Unit::new(vec![
            UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
            UnitSource::new(base, Vec::new()),
        ])
        .expect("two sources make a unit")
    }

    /// A poll that retires the work at its `at`th reading, counting every
    /// reading.
    #[derive(Debug)]
    struct RetireAt
    {
        /// The reading that retires the work, counted from one.
        at: usize,
        /// How many times the work has been polled.
        readings: core::cell::Cell<usize>,
    }

    impl Retirement for RetireAt
    {
        type Retired = ();

        /// Wanted until the `at`th reading, retired from it on.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: one more reading counted; [`Demand::Retired`] once the
        ///   count reaches `at`.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the witness counts the readings a member
        ///   judgement made.
        /// - witness: `compose::tests::a_retired_member_judgement_keeps_nothing_1663`
        #[spec(
            captures: before = self.readings.get(),
            ensures: |ret| self.readings.get() == before.saturating_add(1)
                && matches!(ret, Demand::Retired(())) == (self.readings.get() >= self.at),
        )]
        fn demand(&self) -> Demand<()>
        {
            let reading = self.readings.get().saturating_add(1);
            self.readings.set(reading);
            if reading >= self.at {
                Demand::Retired(())
            }
            else {
                Demand::Wanted
            }
        }
    }

    /// The built-in grammar with one more rule, a form no source writes: a
    /// grammar of another fingerprint, so a tree molded under it is refused
    /// under the built-in one.
    ///
    /// # Specification
    /// trivial.
    fn another_grammar() -> Pbg
    {
        use gandr_surface_grammar::PrecName;
        use gandr_surface_grammar::Provenance;
        use gandr_surface_grammar::Regex;
        use gandr_surface_grammar::Rule;
        use gandr_surface_grammar::RuleName;
        use gandr_surface_grammar::Sort;
        use gandr_surface_grammar::TileLabel;
        use gandr_surface_grammar::built_in_prec_table;

        let precs = built_in_prec_table().expect("the band table builds");
        let prec = precs
            .prec(PrecName("expression.atom"))
            .expect("the band is built in");
        let mut rules = grammar().rules().to_vec();
        rules.push(Rule::with_provenance(
            RuleName("escape_sequence"),
            Provenance("escape_sequence"),
            Sort::Expression,
            prec,
            Regex::tile(TileLabel("escape_sequence")),
        ));
        Pbg::build_table(precs, rules).expect("the grammar builds")
    }

    /// A tree molded under another grammar is the engine's fault on every
    /// lowering route — a unit lowered whole, a document resumed on a closure,
    /// and one lowered onto a judged closure — raised, never carried as the
    /// source's own refusal.
    #[test]
    fn a_tree_of_another_grammar_faults_every_lowering_route()
    {
        use alloc::string::String;
        use alloc::sync::Arc;

        use super::JudgedClosure;
        use super::lower_closure;
        use super::lower_onto_closure;
        use super::lower_parsed_unit;
        use super::lower_resumed_unit;

        let ours = grammar();
        let theirs = another_grammar();
        assert_ne!(
            ours.fingerprint(),
            theirs.fingerprint(),
            "the grammars differ"
        );
        let foreign = || {
            parse(&theirs, SourceText::from("def one = 1 ;\n"))
                .expect("the source parses under the other grammar")
        };
        let engine = |fault: Option<ComposeFault<'_>>| {
            matches!(fault, Some(ComposeFault::Lowering(refusal))
                if refusal.classify() == FailureClass::EngineFault)
        };
        let mut lowerings = LoweringCount::default();
        assert!(
            engine(
                lower_parsed_unit(
                    &ours,
                    foreign(),
                    &alone(),
                    &mut lowerings,
                    &mut gandr_surface_lowering::coincide::Decisions::none()
                )
                .err()
            ),
            "lowered whole"
        );
        let closure = Arc::new(
            lower_closure(
                Arc::new(grammar()),
                String::from("def zero = 0 ;\n"),
                alone(),
                &mut lowerings,
            )
            .expect("the closure is held"),
        );
        assert!(
            engine(
                lower_resumed_unit(
                    &closure,
                    foreign(),
                    &alone(),
                    &mut lowerings,
                    &mut gandr_surface_lowering::coincide::Decisions::none()
                )
                .err()
            ),
            "resumed on a closure, which lowers a tree it does not extend whole"
        );
        let judged = JudgedClosure::new(closure, &HostGrant::UNBOUNDED, CorpusRoot::Fixture)
            .expect("the closure lowers to its end");
        assert!(
            engine(
                lower_onto_closure(
                    &judged,
                    judged.arena(),
                    foreign(),
                    &alone(),
                    &mut lowerings,
                    &mut gandr_surface_lowering::coincide::Decisions::none()
                )
                .err()
            ),
            "onto a judged closure, which leaves a tree it does not extend whole"
        );
    }

    /// A source the lowering refuses whole, as the author's and not the
    /// engine's, is carried as a refused lowering on every route that resumes
    /// a closure: resumed alone, left whole by a judged closure, and laid
    /// after a judged closure's own tree.
    #[test]
    fn a_refused_source_is_carried_on_every_resumed_route()
    {
        use alloc::string::String;
        use alloc::sync::Arc;

        use gandr_surface_syntax::ByteOffset;

        use super::Checking;
        use super::JudgedClosure;
        use super::lower_closure;
        use super::lower_onto_closure;
        use super::lower_resumed_unit;

        let ours = grammar();
        let own = SourceText::from("pure greeting");
        let refused = |lowered: &Lowered<'_>| {
            matches!(*lowered, Lowered::Refused(refusal)
                if refusal.classify() != FailureClass::EngineFault)
        };
        let mut lowerings = LoweringCount::default();
        let closure_text = "def zero = 0 ;\n";
        let closure = Arc::new(
            lower_closure(
                Arc::new(grammar()),
                String::from(closure_text),
                alone(),
                &mut lowerings,
            )
            .expect("the closure is held"),
        );
        let alone_parsed = || parse(&ours, own).expect("the source parses");
        let resumed = lower_resumed_unit(
            &closure,
            alone_parsed(),
            &alone(),
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("a refusal is no fault")
        .into_lowered();
        assert!(refused(&resumed), "resumed alone: {resumed:?}");
        let judged = JudgedClosure::new(
            Arc::clone(&closure),
            &HostGrant::UNBOUNDED,
            CorpusRoot::Fixture,
        )
        .expect("the closure lowers to its end");
        let (whole, checking) = lower_onto_closure(
            &judged,
            judged.arena(),
            alone_parsed(),
            &alone(),
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("a refusal is no fault");
        let whole = whole.into_lowered();
        assert!(
            refused(&whole) && matches!(checking, Checking::Whole),
            "left whole by the judged closure: {whole:?}"
        );
        let text = format!("{closure_text}{}", <&str>::from(own));
        let laid = parse(&ours, own)
            .expect("the source parses")
            .after(closure.tree(), SourceText::from(text.as_str()))
            .expect("the source lays after the closure");
        let (after, checking) = lower_onto_closure(
            &judged,
            judged.arena(),
            laid,
            &pair(ByteOffset::from(closure_text.len())),
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("a refusal is no fault");
        let after = after.into_lowered();
        assert!(
            refused(&after) && matches!(checking, Checking::Whole),
            "laid after the judged closure: {after:?}"
        );
    }

    /// A document is judged on its closure's state only where the closure was
    /// judged as the document is: a closure judged under another grant, or
    /// entering at another entry, is not continued, and the document answers
    /// what judging it whole answers — of its own declarations alone.
    #[test]
    fn a_closure_judged_otherwise_is_not_continued()
    {
        use alloc::string::String;
        use alloc::sync::Arc;

        use gandr_core_term::effect::OperationName;
        use gandr_surface_syntax::ByteOffset;

        use super::Checking;
        use super::Judged;
        use super::JudgedClosure;
        use super::judge_member_after;
        use super::lower_closure;
        use super::lower_onto_closure;
        use super::lower_parsed_unit;

        /// The name and outcome of each declaration `judged` reports.
        ///
        /// # Specification
        /// trivial.
        fn outcomes(judged: Judged<'_>) -> Vec<(String, Outcome)>
        {
            let Ok(Composed::Settled { report, .. }) = judged.settled
            else {
                panic!("the document settles");
            };
            report
                .declarations()
                .iter()
                .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
                .collect()
        }

        /// What the document `own`, laid after `closure_text`, reports judged
        /// under `grant`: after the closure judged under `closure_grant`, and
        /// whole.
        ///
        /// # Specification
        /// trivial.
        fn judged(
            (closure_text, own): (SourceText<'_>, SourceText<'_>),
            (closure_grant, grant): (&HostGrant, &HostGrant),
        ) -> [Vec<(String, Outcome)>; 2]
        {
            let grammar = grammar();
            let mut lowerings = LoweringCount::default();
            let closure = Arc::new(
                lower_closure(
                    Arc::new(grammar.clone()),
                    String::from(<&str>::from(closure_text)),
                    alone(),
                    &mut lowerings,
                )
                .expect("the closure is held"),
            );
            let held = JudgedClosure::new(Arc::clone(&closure), closure_grant, CorpusRoot::Fixture)
                .expect("the closure lowers to its end");
            let text = format!("{}{}", <&str>::from(closure_text), <&str>::from(own));
            let text = SourceText::from(text.as_str());
            let base = ByteOffset::from(<&str>::from(closure_text).len());
            let unit = pair(base);
            let laid = parse(&grammar, own)
                .expect("the document parses")
                .after(closure.tree(), text)
                .expect("the document lays after its closure");
            let (lowering, checking) = lower_onto_closure(
                &held,
                held.arena(),
                laid,
                &unit,
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the document lowers");
            assert!(
                matches!(checking, Checking::After(_)),
                "the document is lowered after the closure"
            );
            let Lowered::Module { module, arena } = lowering.into_lowered()
            else {
                panic!("the document is not refused whole");
            };
            let after = judge_member_after(
                CorpusRoot::Fixture,
                (module, text),
                arena,
                (grant, checking),
                base,
            );
            let Lowered::Module { module, arena } = lower_parsed_unit(
                &grammar,
                parse(&grammar, text).expect("the unit parses"),
                &unit,
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the unit lowers")
            .into_lowered()
            else {
                panic!("the unit is not refused whole");
            };
            let whole = judge_member_after(
                CorpusRoot::Fixture,
                (module, text),
                arena,
                (grant, Checking::Whole),
                base,
            );
            [outcomes(after), outcomes(whole)]
        }

        let reading =
            HostGrant::within([&OperationName::from("read")]).expect("the host offers `read`");
        let [after, whole] = judged(
            (
                SourceText::from("def zero = 0 ;\n"),
                SourceText::from("def fs : Cap {read, write} ;\n"),
            ),
            (&HostGrant::UNBOUNDED, &reading),
        );
        assert_eq!(
            after, whole,
            "after a closure granted otherwise, the document is judged whole"
        );
        assert!(
            matches!(whole.as_slice(), [(name, outcome)]
                if name == "fs" && *outcome != Outcome::Checks(ObligationCount::from(1_usize))),
            "a capability beyond the grant is not owed, and the closure's own declaration is not \
             reported: {whole:?}"
        );

        let [operator, seat] = ["operator", "seat"].map(WorldName::from);
        let entering = HostGrant::UNBOUNDED.entering(vec![operator, seat]);
        let [after, whole] = judged(
            (
                SourceText::from("def zero = 0 ;\n"),
                SourceText::from(
                    "world operator ;\nworld seat ;\ndef moved() -> -F Integer { migrate [seat] { \
                     pure 1 } }\n",
                ),
            ),
            (&entering, &entering),
        );
        assert_eq!(
            after, whole,
            "after a closure that enters at another entry, the document is judged whole"
        );
        assert_eq!(
            whole.last().map(|&(_, ref outcome)| outcome.clone()),
            Some(Outcome::Checks(ObligationCount::from(0_usize))),
            "the document's own worlds hold the entry's capability"
        );
    }

    /// Each source of a component judged once reports its own declarations,
    /// the obligations they owe and the builtins they shadow, and none of its
    /// neighbour's.
    #[test]
    fn each_source_of_a_component_reports_its_own_share()
    {
        use gandr_surface_syntax::ByteOffset;

        use super::Keeping;
        use super::SpellingCount;
        use super::judge_component;
        use super::lower_parsed_unit;
        use crate::component::Member;

        let grammar = grammar();
        let first = "def one : Integer ;";
        let second = "def two : Integer ;\ndef three : Integer ;\ndef add = 1 ;";
        // A component joins its sources with a newline, as the walk lays them.
        let text = format!("{first}\n{second}");
        let base = ByteOffset::from(first.len().saturating_add(1_usize));
        let members = [
            Member {
                start: ByteOffset::from(0_usize),
                end: ByteOffset::from(first.len()),
            },
            Member {
                start: base,
                end: ByteOffset::from(text.len()),
            },
        ];
        let lowering = lower_parsed_unit(
            &grammar,
            parse(&grammar, SourceText::from(text.as_str())).expect("the component parses"),
            &pair(base),
            &mut LoweringCount::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the component lowers");
        let shares: Vec<(Vec<String>, usize, usize)> = judge_component(
            CorpusRoot::Fixture,
            (lowering, SourceText::from(text.as_str())),
            &HostGrant::UNBOUNDED,
            (&members, &mut SpellingCount::default()),
            Keeping::Composed,
        )
        .0
        .into_iter()
        .map(|composed| match composed {
            Ok(Composed::Settled {
                report, shadowed, ..
            }) => (
                report
                    .declarations()
                    .iter()
                    .map(|declaration| declaration.name().to_string())
                    .collect(),
                usize::from(report.ledger()),
                shadowed.len(),
            ),
            Ok(Composed::Refused(refusal)) => panic!("refused whole: {refusal}"),
            Err(fault) => panic!("faulted: {fault}"),
        })
        .collect();
        assert_eq!(
            shares,
            [
                (Vec::from([String::from("one")]), 1_usize, 0_usize),
                (
                    Vec::from([
                        String::from("two"),
                        String::from("three"),
                        String::from("add")
                    ]),
                    2_usize,
                    1_usize
                ),
            ],
            "each source reports its own declarations, debts and shadowed builtins"
        );
    }

    /// An importer reading one base and not another reports the other's
    /// import alone; an importer whose own declaration the lowering refused
    /// reports none, its names past the refusal never read.
    #[test]
    fn an_import_no_lookup_reaches_is_unreached()
    {
        use gandr_surface_lowering::ImportTarget;
        use gandr_surface_lowering::SourceIndex;
        use gandr_surface_lowering::Unit;
        use gandr_surface_lowering::UnitSource;
        use gandr_surface_syntax::ByteOffset;

        use super::Keeping;
        use super::SpellingCount;
        use super::judge_component;
        use super::lower_parsed_unit;
        use crate::component::Member;

        let grammar = grammar();
        let sources = [
            "def seven : Integer ;\ndef seven = 7 ;",
            "def eight : Integer ;\ndef eight = 8 ;",
            "import \"./seven.gandr\" ;\nimport \"./eight.gandr\" ;\ndef value : Integer ;\ndef \
             value = seven ;",
            "import \"./eight.gandr\" ;\ndef broken : Integer ;\ndef broken = nowhere ;",
        ];
        // A component joins its sources with a newline, as the walk lays them.
        let text = sources.join("\n");
        let mut members = Vec::new();
        let mut start = 0_usize;
        for source in sources {
            let end = start.saturating_add(source.len());
            members.push(Member {
                start: ByteOffset::from(start),
                end: ByteOffset::from(end),
            });
            start = end.saturating_add(1_usize);
        }
        let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
        let unit = Unit::new(
            members
                .iter()
                .zip([
                    Vec::new(),
                    Vec::new(),
                    vec![on(0_usize), on(1_usize)],
                    vec![on(1_usize)],
                ])
                .map(|(member, imports)| UnitSource::new(member.start, imports))
                .collect(),
        )
        .expect("four sources make a unit");
        let lowering = lower_parsed_unit(
            &grammar,
            parse(&grammar, SourceText::from(text.as_str())).expect("the component parses"),
            &unit,
            &mut LoweringCount::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the component lowers");
        let unreached: Vec<Vec<&str>> = judge_component(
            CorpusRoot::Fixture,
            (lowering, SourceText::from(text.as_str())),
            &HostGrant::UNBOUNDED,
            (&members, &mut SpellingCount::default()),
            Keeping::Composed,
        )
        .0
        .into_iter()
        .map(|composed| match composed {
            Ok(Composed::Settled { unreached, .. }) => unreached
                .iter()
                .map(|span| {
                    text.get(usize::from(span.start()) .. usize::from(span.end()))
                        .unwrap_or_default()
                })
                .collect(),
            Ok(Composed::Refused(refusal)) => panic!("refused whole: {refusal}"),
            Err(fault) => panic!("faulted: {fault}"),
        })
        .collect();
        assert_eq!(
            unreached,
            [
                Vec::new(),
                Vec::new(),
                Vec::from(["import \"./eight.gandr\" ;"]),
                Vec::new()
            ],
            "the importer reports the import it reads nothing through; the refused one none"
        );
    }

    /// #1663: a member judgement polled to retirement before its second
    /// declaration answers retired, and so does one the poll after its last
    /// declaration retires before the settle; one whose poll never retires it
    /// reads the poll once before each declaration and once before the settle,
    /// and answers what the judgement nobody polls answers, its table too.
    #[test]
    fn a_retired_member_judgement_keeps_nothing_1663()
    {
        use gandr_surface_syntax::ByteOffset;

        use super::Checking;
        use super::judge_member_after;
        use super::judge_member_after_retiring;
        use super::judge_member_tabled;
        use super::judge_member_tabled_retiring;

        let grammar = grammar();
        let source = SourceText::from("def one = 1 ;\ndef two = 2 ;\ndef three = 3 ;\n");
        let lowered = || {
            let Lowered::Module { module, arena } =
                lower_source(&grammar, source, &mut LoweringCount::default())
                    .expect("the module lowers")
                    .into_lowered()
            else {
                panic!("the module is read");
            };
            (module, arena)
        };
        let base = ByteOffset::from(0_usize);
        let judged = |at| {
            let poll = RetireAt {
                at,
                readings: core::cell::Cell::new(0),
            };
            let (module, arena) = lowered();
            let answer = judge_member_after_retiring(
                CorpusRoot::Strict,
                (module, source),
                arena,
                (&HostGrant::UNBOUNDED, Checking::Whole),
                base,
                &poll,
            );
            (answer, poll.readings.get())
        };
        let (second, read) = judged(2);
        assert!(
            matches!(second, Polled::Retired((), ())),
            "the poll before the second declaration retires the judgement"
        );
        assert_eq!(read, 2, "and the third declaration is never polled for");
        let (settling, read) = judged(4);
        assert!(
            matches!(settling, Polled::Retired((), ())),
            "the poll after the last declaration retires it before the settle"
        );
        assert_eq!(read, 4, "the fourth reading is the settle's");
        let (never, read) = judged(5);
        let Polled::Whole(polled) = never
        else {
            panic!("a poll never retired answers whole");
        };
        assert_eq!(
            read, 4,
            "polled once before each of the three declarations and once before the settle"
        );
        assert!(
            matches!(polled.settled, Ok(Composed::Settled { .. })),
            "the module settles"
        );
        let (module, arena) = lowered();
        let whole = judge_member_after(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            base,
        );
        assert_eq!(
            polled.settled, whole.settled,
            "and answers what the judgement nobody polls answers"
        );

        let unit = alone();
        let tabled = |at| {
            let poll = RetireAt {
                at,
                readings: core::cell::Cell::new(0),
            };
            let (module, arena) = lowered();
            let answer = judge_member_tabled_retiring(
                CorpusRoot::Strict,
                (module, source),
                arena,
                (&HostGrant::UNBOUNDED, Checking::Whole),
                (&unit, base),
                &poll,
            );
            (answer, poll.readings.get())
        };
        let (second, read) = tabled(2);
        assert!(
            matches!(second, Polled::Retired((), ())) && read == 2,
            "the tabled judgement is retired alike"
        );
        let (never, read) = tabled(5);
        let Polled::Whole((polled, polled_table)) = never
        else {
            panic!("a tabled judgement never retired answers whole");
        };
        assert_eq!(read, 4, "and is polled as the untabled one is");
        assert!(
            matches!(polled_table, Maybe::Present(_)),
            "its table is made"
        );
        let (module, arena) = lowered();
        let (whole, whole_table) = judge_member_tabled(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            (&unit, base),
        );
        assert_eq!(
            (polled.settled, polled_table),
            (whole.settled, whole_table),
            "and answers what the tabled judgement nobody polls answers"
        );
    }
}
