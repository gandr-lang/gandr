//! The item source: one lowered revision, offered to the incremental checker
//! as its items.
//!
//! # One item per declaration the lowering did not refuse
//!
//! The checker's input for a module is the dispatcher's [`adapt`]: every
//! declaration the lowering did not refuse, in admission order. The item
//! source keys each of those by its declared name and leaves the refused ones
//! out, so the program the incremental checker resumes over holds exactly the
//! declarations the batch judgement checks, at the same admission positions.

use core::fmt;

use anodized::spec;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemSource;
use gandr_core_incremental::Program;
use gandr_core_incremental::ProgramError;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::adapt;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a revision's fault names no span of its text.
    pub mod fault_span {
        /// The reason no span is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal is about the run, not about a position in the text.
            Run,
        }
    }
}

/// The program `module` lowers to, over the `arena` it was minted in.
///
/// # Specification
/// - requires: `module` was lowered into `arena`.
/// - ensures: one item per declaration the lowering did not refuse, in
///   admission order, keyed by the declaration's name as written and carrying
///   exactly the declaration [`adapt`] gives the checker for it.
/// - provides: the program the incremental checker resumes over, which holds
///   the declarations the batch judgement checks and no other.
/// - fails: [`ProgramError::PositionOrder`] when two kept declarations'
///   admission positions do not ascend.
/// - panics: none.
///
/// # Errors
/// - [`ProgramError::PositionOrder`]: the lowering assigned positions out of
///   order.
///
/// # Adequacy
/// - hypothesis: L3 — a lowered module with a refused middle declaration, an
///   explicit signature and an owed body; exact name keys, skipped admission
///   positions and declaration payloads distinguish retaining refusals,
///   reordering, misnaming and losing signature/body/origin data. Arena
///   provenance is a caller premise, not inferred from local identifiers.
/// - witness: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`
#[spec(
    ensures: |ret| match ret {
    Ok(ref result) => {
        result.items().len()
            == module
                .declarations()
                .iter()
                .filter(|lowered| {
                    !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                })
                .count()
            && result
                .items()
                .iter()
                .zip(
                    module
                        .declarations()
                        .iter()
                        .filter(|lowered| {
                            !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                        }),
                )
                .all(|(item, lowered)| {
                    let declaration = item.declaration();
                    item.key().as_ref() == lowered.name().as_ref().as_bytes()
                        && declaration.constant() == lowered.constant()
                        && usize::from(declaration.origin())
                            == usize::from(lowered.origin())
                        && match (lowered.outcome(),declaration.content()) {
                            (DeclarationOutcome::Completed {declared_type,body},&gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(signature),body:Maybe::Present(value)}) => signature == declared_type && value == body,
                            (DeclarationOutcome::Uncompleted {declared_type},&gandr_core_checker::DeclarationContent::Value {signature:Maybe::Present(signature),body:Maybe::Absent(_)}) => signature == declared_type,
                            (DeclarationOutcome::Bodied {body},&gandr_core_checker::DeclarationContent::Value {signature:Maybe::Absent(_),body:Maybe::Present(value)}) => value == body,
                            _ => false,
                        }
                })
    }
    Err(ProgramError::PositionOrder { ordinal, position, previous }) => {
        position <= previous
            && module
                .declarations()
                .iter()
                .filter(|lowered| {
                    !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                })
                .nth(usize::from(ordinal))
                .is_some_and(|lowered| lowered.constant() == position)
            && usize::from(ordinal)
                .checked_sub(1_usize)
                .and_then(|before| {
                    module
                        .declarations()
                        .iter()
                        .filter(|lowered| {
                            !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                        })
                        .nth(before)
                })
                .is_some_and(|lowered| lowered.constant() == previous)
    }
},
)]
#[inline]
pub fn program(
    module: &LoweredModule<'_>,
    arena: CoreArena,
) -> Result<Program, ProgramError>
{
    let keys = module
        .declarations()
        .iter()
        .filter(|lowered| !matches!(lowered.outcome(), DeclarationOutcome::Refused(_)))
        .map(|lowered| ItemKey::from(lowered.name().as_ref()));
    let items = keys
        .zip(adapt(module))
        .map(|(key, declaration)| Item::new(key, declaration))
        .collect();
    Program::new(arena, items)
}

/// One revision of a source, as the item source reads it: its full text.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Revision(String);

impl Revision
{
    /// The revision's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(self.0.as_str())
    }
}

impl From<&str> for Revision
{
    /// The revision whose text is `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(String::from(text))
    }
}

impl From<String> for Revision
{
    /// The revision whose text is `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

/// Why a revision could not be offered as items.
///
/// The item seam's error cannot borrow the revision it was handed, so a
/// refusal of the revision as a whole crosses as its class and the span it
/// names; the session, which keeps the text in reach, reports the refusal
/// itself.
///
/// # Specification
/// - requires: nothing.
/// - ensures: retains the stage failure, or the whole-revision refusal class
///   and optional source span.
/// - executable: none — The error value has no original lowering operation or
///   revision; refused specifies the retained class/span, and the item-source
///   witness observes the source boundary.
///
/// # Adequacy
/// - hypothesis: L3 — accepted declarations and a whole-revision refusal,
///   observed at exact keys, failure class and source extent; the formatter
///   witness distinguishes lost fields and swallowed sink failures.
/// - witness: `tests::items::the_item_source_offers_a_revision_or_names_its_fault`
/// - witness: `tests::items::revision_faults_retain_fields_and_sink_refusals`
#[derive(Clone, Debug)]
pub enum RevisionFault
{
    /// The composition faulted before the lowering read a module, with a
    /// fault that borrows nothing of the text: the parser could not commit its
    /// tree.
    Faulted(ComposeFault<'static>),
    /// The lowering refused the revision as a whole, before any declaration
    /// existed to become an item.
    Refused
    {
        /// The refusal's failure class: the engine-fault class when the
        /// lowering faulted, the author's or the fragment's otherwise.
        class: FailureClass,
        /// The bytes the refusal covers.
        span: Maybe<ByteSpan, fault_span::Absent>,
    },
    /// The lowered declarations' admission positions do not ascend.
    Unordered(ProgramError),
}

impl RevisionFault
{
    /// The fault a refusal of the whole revision crosses the seam as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: preserves the refusal class and any source span; a run-level
    ///   refusal remains explicitly spanless.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a top-level expression refused as a whole, observed
    ///   at its exact failure class and source extent. Wrong class, erased span
    ///   and shifted bytes are distinguishable; run-level absence is specified
    ///   by the predicate but not reached by this source witness.
    /// - witness: `tests::items::the_item_source_offers_a_revision_or_names_its_fault`
    #[spec(
        ensures: |ret| {
    matches!(
        ret, Self::Refused { class, span } if class == refusal.classify() && match (span,
        refusal.span()) { (Maybe::Present(found), Maybe::Present(expected)) => found ==
        expected, (Maybe::Absent(fault_span::Absent::Run), Maybe::Absent(_)) => true, _
        => false, }
    )
},
    )]
    fn refused(refusal: &LoweringRefusal<'_>) -> Self
    {
        Self::Refused {
            class: refusal.classify(),
            span: match refusal.span() {
                | Maybe::Present(span) => Maybe::Present(span),
                | Maybe::Absent(_) => Maybe::Absent(fault_span::Absent::Run),
            },
        }
    }
}

impl fmt::Display for RevisionFault
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the underlying stage fault, or the refusal class and
    ///   every retained source-span endpoint.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — The formatter exposes neither emitted text nor
    ///   readable sink state; the witness observes semantic fields and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — span-bearing and spanless refusals plus a
    ///   position-order fault; exact field values and sink errors distinguish
    ///   omitted metadata and swallowed writes without pinning sentences.
    /// - witness: `tests::items::revision_faults_retain_fields_and_sink_refusals`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Faulted(ref fault) => fault.fmt(f),
            | Self::Refused { class, span } => {
                write!(f, "the lowering refused the revision as a whole ({class})")?;
                match span {
                    | Maybe::Present(span) => write!(f, " at {span}"),
                    | Maybe::Absent(_) => Ok(()),
                }
            },
            | Self::Unordered(ref error) => error.fmt(f),
        }
    }
}

impl core::error::Error for RevisionFault
{
}

/// The dispatcher's parse and lowering, as the incremental checker's item
/// source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: retains the grammar used by every offered revision.
/// - executable: none — The carrier stores a grammar but has no revision or
///   call boundary. Its items method states the observable source relationship.
///
/// # Adequacy
/// - hypothesis: L3 — accepted named declarations and a refused top-level
///   expression through the built-in grammar; item identities and the refusal
///   span distinguish a stale or misconfigured item source.
/// - witness: `tests::items::the_item_source_offers_a_revision_or_names_its_fault`
#[repr(transparent)]
#[derive(Debug)]
pub struct SurfaceItems
{
    /// The grammar every revision is parsed under.
    grammar: Pbg,
}

impl SurfaceItems
{
    /// The item source parsing under `grammar`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(grammar: Pbg) -> Self
    {
        Self { grammar }
    }
}

impl ItemSource for SurfaceItems
{
    type Error = RevisionFault;
    type Revision = Revision;

    /// The program `revision` lowers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the revision parsed and lowered once by the dispatcher's
    ///   [`lower_source`], and the module's [`program`].
    /// - fails: [`RevisionFault::Faulted`] when the parser cannot commit its
    ///   tree; [`RevisionFault::Refused`] when the lowering refuses the
    ///   revision as a whole; [`RevisionFault::Unordered`] as [`program`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — modules with distinct names and a top-level
    ///   expression refused whole; exact admitted keys and refusal class/span
    ///   distinguish stale revision input, invented names and misplaced
    ///   diagnostics. The predicate checks source membership and span validity
    ///   without replaying parse or lowering; program specifies exact
    ///   lowered-item correspondence.
    /// - witness: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`
    /// - witness: `tests::items::the_item_source_offers_a_revision_or_names_its_fault`
    #[spec(
        ensures: |ret| match ret {
    Ok(ref result) => {
        result
            .items()
            .iter()
            .all(|item| {
                core::str::from_utf8(item.key().as_ref())
                    .is_ok_and(|name| !name.is_empty() && revision.0.contains(name))
            })
    }
    Err(RevisionFault::Refused { span: Maybe::Present(span), .. }) => {
        revision.text().fragment(span).is_ok()
    }
    Err(_) => true,
},
    )]
    #[inline]
    fn items(
        &self,
        revision: &Revision,
    ) -> Result<Program, RevisionFault>
    {
        let mut lowerings = LoweringCount::default();
        let lowering = match lower_source(&self.grammar, revision.text(), &mut lowerings) {
            | Ok(lowering) => lowering,
            | Err(ComposeFault::Lowering(ref refusal)) => {
                return Err(RevisionFault::refused(refusal));
            },
            | Err(ComposeFault::Parse(error)) => {
                return Err(RevisionFault::Faulted(ComposeFault::Parse(error)));
            },
            | Err(ComposeFault::Settle(fault)) => {
                return Err(RevisionFault::Faulted(ComposeFault::Settle(fault)));
            },
            | Err(ComposeFault::Readmission(readmitted)) => {
                return Err(RevisionFault::Faulted(ComposeFault::Readmission(
                    readmitted,
                )));
            },
        };
        match lowering.into_lowered() {
            | Lowered::Module { module, arena } => {
                program(&module, arena).map_err(RevisionFault::Unordered)
            },
            | Lowered::Refused(ref refusal) => Err(RevisionFault::refused(refusal)),
        }
    }
}
