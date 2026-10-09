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
/// - hypothesis: L3 — the surfaces are the key, the declaration and the
///   position of each item, separated by a module whose middle declaration is
///   refused, every item asserted at its exact key and at the adapted
///   declaration of the same position.
/// - witness: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`
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
    /// trivial.
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
    /// trivial.
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
    /// - hypothesis: L3 — the surfaces are a module offered as items and a
    ///   revision refused whole, each asserted at its exact program or class.
    /// - witness: `tests::items::the_item_source_offers_a_revision_or_names_its_fault`
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
