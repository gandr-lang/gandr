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
//! shadowed builtins, inferred exits and runs and the obligations its
//! declarations owe, and shares the component's origins, failures, program
//! and kernel artifact. A source given alone is composed over its import
//! closure, its own text last ([`judge_member`]), which is the component it
//! makes on its own: the session's unit.
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
use alloc::sync::Arc;
use core::fmt;

use anodized::spec;
use gandr_core_checker::AbstractType;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::ComponentOrdinal;
use gandr_core_checker::Declaration;
use gandr_core_checker::HostGrant;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Nesting;
use gandr_core_checker::ObligationCount;
use gandr_core_checker::OriginToken;
use gandr_core_checker::SealSite;
use gandr_core_checker::SealingSite;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::StructuredName;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::SettleFault;
use gandr_surface_corpus::SettleReport;
use gandr_surface_corpus::settle;
use gandr_surface_diagnostics::Failures;
use gandr_surface_diagnostics::Spellings;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::InferredExit;
use gandr_surface_lowering::InferredRun;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::Sealing;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::component::Member;
use crate::evaluate::Program;
use crate::exercised::Exercised;

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
    /// - witness: `corpus::corpus::sweeps::every_width_composes_the_corpus_alike`
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
        /// their failures name, spelled while the arena was at hand: the
        /// table a refusal's types are read from.
        spellings: Spellings,
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
/// - witness: `corpus::corpus::sweeps::every_width_composes_the_corpus_alike`
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
    pub fn admit(mut self) -> Result<EncodedArtifact, bridge::Readmitted>
    {
        let readmission = readmitted(&mut self.arena, &self.verdicts)?;
        Ok(readmission.export(self.names))
    }
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
    ///   includes the declaration's admission position.
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
                    bridge::Outcome::Refused(refusal) => {
                        write!(f, "the bridge refused to offer it ({})", refusal.classify())
                    },
                    bridge::Outcome::Data { .. }
                    | bridge::Outcome::Defined { .. }
                    | bridge::Outcome::Assumed { .. }
                    | bridge::Outcome::Marked(_)
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
    use anodized::spec;
    use gandr_core_term::CoreArena;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::lower_unit;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_syntax::SyntaxTree;

    use super::LoweringCount;

    /// Lower the sources `unit` lays out in `tree` into `arena` against the
    /// empty outermost scope, counting each of them in `lowerings`.
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
        )
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
    lower_parsed(grammar, parsed, lowerings)
}

/// Lower one source the parser has committed: [`lower_source`] past its
/// parse.
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
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    lower_parsed_unit(grammar, parsed, &Unit::single(), lowerings)
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
    lower_parsed_unit(grammar, parsed, unit, lowerings)
}

/// Lower the sources `unit` lays end to end in the tree `parsed` committed:
/// [`lower_unit_source`] past its parse.
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
/// - hypothesis: L3 — every witness of [`lower_parsed`] lowers through here.
/// - witness: `compose::tests::each_composition_lowers_once`
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
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
) -> Result<Lowering<'source>, ComposeFault<'source>>
{
    let obligations = parsed.obligations().to_vec();
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let lowered = match lowering::lower(grammar, &tree, unit, &mut arena, lowerings) {
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

/// Judge and settle one lowered module, its kernel admission left to run.
///
/// # Specification
/// - requires: `module` was lowered from `text` into `arena`; `root` is the
///   corpus root the source sits under.
/// - ensures: the module is adapted to the checker's input, judged with its
///   held capabilities bounded by `grant` minted into `arena`, built into a
///   [`Program`] and settled under `root`, the program running each declaration
///   that states a run outcome. The settled composition carries one report per
///   declared name, the exercised rows its settled declarations carry, the
///   refusals of the declarations refused at their own form, which no
///   expectation can state, the lowering's origin table, moved rather than
///   copied, the spellings of the types its checker refusals compare and its
///   failures name, each under its binders' names in `text`, the failures
///   themselves, every builtin the source shadowed, every exit the lowering
///   inferred, every run the checker inferred, the program, and no kernel
///   artifact yet ([`admitted::Absent::Pending`]); a settle fault is carried in
///   its place. The admission holds the arena the verdicts were judged over,
///   the verdicts and the module's structured names.
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
    let last = Member {
        start: base,
        end: ByteOffset::from(text.as_ref().len()),
    };
    let (projected, admission) = judge_members(root, (module, text), arena, grant, (&[], last));
    Judged {
        settled: projected.last,
        admission,
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
    /// The types its checker refusals compare and the unit's failures name.
    spellings: Spellings,
    /// The builtins it shadowed.
    shadowed: Vec<ShadowedBuiltin>,
    /// The exits the lowering inferred in it.
    inferred: Vec<InferredExit>,
    /// The runs the checker inferred in it.
    runs: Vec<InferredRun>,
}

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
///   of the ledger, the obligations its declarations owe; its spellings are its
///   report's; the origins, failures and program are the unit's, shared. A
///   source that is the whole unit reports everything, nothing copied. A settle
///   fault is every source's. The admission holds the arena, the verdicts and
///   the unit's structured names.
/// - fails: never; a settle fault is carried.
/// - panics: none.
/// - intension: one check, one program, one settle comparison per unit; the
///   unit-wide tables are copied once for each source but the last, which takes
///   them.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond judged as one component reports each source's
///   own declarations at each source, and a unit of one source reports all of
///   its own.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::a_module_settles_every_declaration_once`
#[spec(ensures: |ref ret| ret.0.earlier.len() == earlier.len())]
fn judge_members<'source>(
    root: CorpusRoot,
    (mut module, text): (LoweredModule<'source>, SourceText<'source>),
    mut arena: CoreArena,
    grant: &HostGrant,
    (earlier, last): (&[Member], Member),
) -> (Projected<'source>, Admission)
{
    let declarations = adapt(&module);
    let grants = grant.grants(&mut arena);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.grant(grants);
    let verdicts = check_module(&mut context, &declarations);
    let names = module.structured_names();
    let mut program = Program::new(&arena, &module, &verdicts);
    let projected = match settle(root, &arena, &module, &verdicts, &mut program) {
        Ok(report) => {
            let failures = Failures::of(&verdicts);
            located(module.origins_mut(), &verdicts);
            let unit = Unitwide {
                unstatable: unstatable(&module),
                runs: inferred_runs(&module, &verdicts),
                failures: &failures,
            };
            let whole = earlier.is_empty() && usize::from(last.start) == 0_usize;
            let earlier = earlier
                .iter()
                .map(|&member| {
                    let own = owned(&report, (&module, &verdicts), member);
                    let held = share(member, own, (&arena, &module, text), &unit);
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
            let last_share = share(last, own, (&arena, &module, text), &unit);
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
    (projected, Admission {
        arena,
        verdicts,
        names,
    })
}

/// What a judged unit holds once for all of its sources, read by [`share`].
#[derive(Debug)]
struct Unitwide<'unit, 'source>
{
    /// The unit's declarations refused at their own form.
    unstatable: Vec<LoweringRefusal<'source>>,
    /// The runs the checker inferred over the unit.
    runs: Vec<InferredRun>,
    /// The failures the checking machine kept over the unit.
    failures: &'unit Failures,
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
///   obligations left to the sibling.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
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
/// `report` already its own.
///
/// # Specification
/// - requires: `report` is [`owned`] of `member`, or the whole unit's for a
///   source that is the whole unit; `unit` is the unit's.
/// - ensures: `report`, the exercised rows it carries, the spellings of the
///   types its checker refusals compare and the unit's failures name, and of
///   the unit's refusals at a declaration's own form, shadowed builtins,
///   inferred exits and inferred runs, those written in `member` — starting
///   within its own bytes, its end included — a refusal with no span kept.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`judge_members`].
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`
#[spec(ensures: |ref ret| ret.shadowed.iter().all(|shadow| member.start <= shadow.span.start() && shadow.span.start() <= member.end)
    && ret.runs.iter().all(|run| member.start <= run.span.start() && run.span.start() <= member.end))]
fn share<'source>(
    member: Member,
    report: SettleReport<'source>,
    (arena, module, text): (&CoreArena, &LoweredModule<'source>, SourceText<'source>),
    unit: &Unitwide<'_, 'source>,
) -> Share<'source>
{
    let own = |span: ByteSpan| member.start <= span.start() && span.start() <= member.end;
    let exercised = Exercised::of(arena, module, &report);
    let spellings = Spellings::of(
        arena,
        module,
        &report,
        unit.failures,
        (module.origins(), text),
    );
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
    Share {
        report,
        exercised,
        unstatable,
        spellings,
        shadowed,
        inferred,
        runs,
    }
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
        runs: share.runs,
        kernel: Maybe::Absent(admitted::Absent::Pending),
        program,
    }
}

/// Judge what the lowering made of one component once, and project the
/// composition onto each of its sources.
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
///   source's.
/// - provides: the walk's verdict at each source of a component, the component
///   lowered and checked once.
/// - fails: per source, as [`judge_module`]: a kernel disagreement is every
///   source's [`ComposeFault::Readmission`], since the component's environment
///   could not be built past it; otherwise a settle fault is every source's
///   [`ComposeFault::Settle`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond judged whole reports each source's own
///   declarations, each certificate holding the base's segments once, first;
///   the corpus at every width composes alike.
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `corpus::corpus::sweeps::every_width_composes_the_corpus_alike`
#[spec(ensures: |ref ret| ret.len() == members.len())]
pub fn judge_component<'source>(
    root: CorpusRoot,
    (lowering, text): (Lowering<'source>, SourceText<'source>),
    grant: &HostGrant,
    members: &[Member],
) -> Vec<Result<Composed<'source>, ComposeFault<'source>>>
{
    let Some((&last, earlier)) = members.split_last()
    else {
        return Vec::new();
    };
    match lowering.into_lowered() {
        Lowered::Module { module, arena } => {
            let (projected, admission) =
                judge_members(root, (module, text), arena, grant, (earlier, last));
            match admission.admit() {
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
            }
        },
        Lowered::Refused(refusal) => members
            .iter()
            .map(|_| Ok(Composed::Refused(refusal)))
            .collect(),
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

/// The lowering's origin table, with every node the checker's elaborations
/// minted located at the written node it elaborates.
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
///   before any node of that judgement was recorded in it.
/// - ensures: `origins` with [`OriginTable::carry`] applied to every node each
///   elaboration reports minting beside the node it stands for; `origins`
///   itself when no body was elaborated.
/// - provides: the table a second-run refusal is located through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fold nesting its call and its bound twin, each refused
///   by the rule it tells apart, refuse at one case block.
/// - witness: `entry::tests::a_second_run_refusal_is_located_where_its_bound_spelling_is`
#[spec(captures: [declarations = origins.declaration_count(), recorded = origins.recorded_count()],
    ensures: origins.declaration_count() == declarations && origins.recorded_count() >= recorded)]
fn located(
    origins: &mut OriginTable,
    verdicts: &ModuleReport,
)
{
    let elaborations = verdicts.nested_elaborations();
    if elaborations.is_empty() {
        return;
    }
    let carried: Vec<_> = elaborations
        .values()
        .flat_map(|elaboration| elaboration.carried().iter().copied())
        .collect();
    let binds: Vec<_> = elaborations
        .values()
        .flat_map(|elaboration| elaboration.binds().iter().copied())
        .collect();
    origins.carry(&carried, &binds);
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
/// - witness: `corpus::corpus::sweeps::every_width_composes_the_corpus_alike`
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
                    | DeclarationOutcome::Abstract(_),
                    ..,
                ) => None,
            }
        })
        .collect()
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
///   names; a data declaration carries its native signature, shared with the
///   lowered module, and a sealed abstract type its kind, representation,
///   extent and site. A refused declaration is not offered.
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
            && match lowered.outcome() {
                DeclarationOutcome::Completed { declared_type, body } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(declared_type),body:Maybe::Present(body)},
                DeclarationOutcome::Uncompleted { declared_type } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(declared_type),body:Maybe::Absent(body::Absent::Hole)},
                DeclarationOutcome::Bodied { body } =>
                    actual.content() == &gandr_core_checker::DeclarationContent::Value {signature:Maybe::Absent(signature::Absent::Unsigned),body:Maybe::Present(body)},
                DeclarationOutcome::Data(index) =>
                    matches!(*actual.content(), gandr_core_checker::DeclarationContent::Data(ref held) if module.data(index) == Maybe::Present(held)),
                DeclarationOutcome::Abstract(sealing) =>
                    *actual.content() == gandr_core_checker::DeclarationContent::Abstract(abstract_type(sealing)),
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
            DeclarationOutcome::Abstract(sealing) => {
                declarations.push(Declaration::abstract_type(
                    lowered.constant(),
                    abstract_type(sealing),
                    OriginToken::from(usize::from(lowered.origin())),
                ));
                continue;
            },
            DeclarationOutcome::Refused(_) => continue,
        };
        declarations.push(
            Declaration::new(
                lowered.constant(),
                declared,
                defined,
                OriginToken::from(usize::from(lowered.origin())),
            )
            .lawful(module.laws(lowered).to_vec()),
        );
    }
    declarations
}

/// The checker's abstract type for the sealing the lowering recorded: its
/// kind, representation and extent, at the site its sealing module and
/// component number.
///
/// # Specification
/// trivial.
fn abstract_type(sealing: Sealing) -> AbstractType
{
    AbstractType::new(
        sealing.kind,
        sealing.representation,
        sealing.extent,
        SealSite::new(
            SealingSite::from(usize::from(sealing.sealing)),
            ComponentOrdinal::from(usize::from(sealing.component)),
        ),
    )
}

/// Have the kernel re-derive every declaration in `verdicts` the checker
/// accepted.
///
/// # Specification
/// - requires: `verdicts` was judged over `arena`.
/// - ensures: succeeds with the readmission when every accepted declaration
///   crossed as a definition or an axiom, or stays on the checker's side as a
///   static definition or as an effectful one the bridge refuses by its
///   effectful former; a refused declaration crosses as its mark, a declaration
///   withheld because it names a refused one carries that one's reason, a
///   declaration holding a term hole or the unknown type stays behind as the
///   user absence it is, and a declaration holding a session stays behind on
///   the checker's side, the kernel having no session former, so none of these
///   is a disagreement.
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
    Ok(ref readmission) => readmission.readmitted().len() == verdicts.judged().len()
        && readmission.readmitted().iter().zip(verdicts.judged()).all(|(crossed, judged)|
            crossed.constant() == judged.constant() && (matches!(*crossed.outcome(),
                bridge::Outcome::Defined { .. } | bridge::Outcome::Assumed { .. }
                    | bridge::Outcome::Data { .. }
                    | bridge::Outcome::Marked(_) | bridge::Outcome::Static
                    | bridge::Outcome::Refused(bridge::Refusal::Withheld { .. } | bridge::Refusal::WithheldData { .. }
                        | bridge::Refusal::Hole { .. } | bridge::Refusal::Unknown { .. }
                        | bridge::Refusal::Session { .. }))
                || matches!(*crossed.outcome(), bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }) if residence(former) == Residence::Checker))),
    Err(ref fault) =>
        verdicts.judged().iter().any(|judged| judged.constant() == fault.constant())
            && (matches!(*fault.outcome(), bridge::Outcome::Rejected(_)
                | bridge::Outcome::Refused(bridge::Refusal::DanglingNode { .. }
                    | bridge::Refusal::Cyclic { .. } | bridge::Refusal::CertificateDeclined { .. }
                    | bridge::Refusal::MachineInvariant))
                || matches!(*fault.outcome(), bridge::Outcome::Refused(bridge::Refusal::OutOfFragment { former, .. }) if residence(former) == Residence::Kernel)),
})]
fn readmitted(
    arena: &mut CoreArena,
    verdicts: &ModuleReport,
) -> Result<bridge::Readmission, bridge::Readmitted>
{
    let readmission = bridge::readmit(arena, verdicts);
    for readmitted in readmission.readmitted() {
        match *readmitted.outcome() {
            bridge::Outcome::Data { .. }
            | bridge::Outcome::Defined { .. }
            | bridge::Outcome::Assumed { .. }
            | bridge::Outcome::Marked(_)
            | bridge::Outcome::Static
            | bridge::Outcome::Refused(
                bridge::Refusal::Withheld { .. }
                | bridge::Refusal::WithheldData { .. }
                | bridge::Refusal::Hole { .. }
                | bridge::Refusal::Unknown { .. }
                | bridge::Refusal::Session { .. },
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
                return Err(readmitted.clone());
            },
        }
    }
    Ok(readmission)
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
///   exercise, a scope, a recorded run or ride, a flow at a universe above
///   level zero and a memory form; the kernel's for every pure former, and for
///   a recursion's stage, which no source writes and the checker never lets a
///   declaration carry, so its refusal is the checker's fault.
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
        | UnadmittedFormer::Reset
        | UnadmittedFormer::Shift
        | UnadmittedFormer::Capability
        | UnadmittedFormer::Exercise
        | UnadmittedFormer::Scope
        | UnadmittedFormer::Run
        | UnadmittedFormer::HigherFlow
        | UnadmittedFormer::Memory => Residence::Checker,
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
    use gandr_core_checker::HostGrant;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
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
            SourceText::from("def greeting = \"hello\" ;\npure greeting"),
            &mut lowerings,
        );
        let Ok(Composed::Refused(refusal)) = composed
        else {
            panic!("a top-level expression refuses the module");
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
            FailureClass::Unrepresentable,
            "the fragment cannot represent it"
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
                true,
                &[(gandr_surface_parser::Oblig::UnmoldedTok, 12_usize, 13_usize)][..],
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
            3_usize,
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
                r#"@[ refuses("OutOfFragment") ] def f @[a : Type] (x: a) -> -F a { return x }
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
            matches!(unstatable.as_slice(), [LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unadmitted,
                ..
            }]),
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
        let admission = readmitted(&mut arena, &verdicts)
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
        let Err(fault) = readmitted(&mut foreign, &verdicts)
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
            let readmission =
                readmitted(&mut arena, &verdicts).expect("the kernel re-derives every acceptance");
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
            super::located(module.origins_mut(), &verdicts);
            let spellings = super::Spellings::of(
                &arena,
                &module,
                &report,
                &failures,
                (module.origins(), SourceText::from(source)),
            );
            let shadowed = module.recognition().shadowed().to_vec();
            let inferred = module.inferred_exits().to_vec();
            let runs = super::inferred_runs(&module, &verdicts);
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
    fn form_refusals_retain_admission_order()
    {
        let grammar = grammar();
        let source = SourceText::from(
            "def first @[a : Type] (x: a) -> -F a { return x }\n\
             def broken = missing ;\n\
             def value = 3 ;\n\
             def last @[a : Type] (x: a) -> -F a { return x }",
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
                | DeclarationOutcome::Abstract(_)
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
                Form::Explicit,
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
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::Refused(_)) => {
                panic!("`{wanted}` lowers a signature, not {other:?}")
            },
        };
        let body = |wanted: &str| match outcome(wanted) {
            DeclarationOutcome::Completed { body, .. } => body,
            other @ (DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Abstract(_)
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
                        Form::Sugared,
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
                    Form::Sugared,
                ),
            ),
            (
                "pure_pair",
                "(1, \"a\")",
                present_computation(
                    &printer,
                    CoreNode::Computation(suspended),
                    PageWidth::from(100_u32),
                    Form::Sugared,
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
                Form::Explicit,
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
                Form::Sugared,
            )
            .expect("the arm lays out");
            assert_eq!(
                (presentation.to_string(), presentation.fidelity()),
                (String::from(expected), Fidelity::Faithful),
                "restored, the bind prints as the nested call written; unrestored, as the bind"
            );
        }
    }
}
