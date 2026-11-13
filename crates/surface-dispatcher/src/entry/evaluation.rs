//! What a run of one declaration came to: its value spelled, or the class
//! of the stop and what the stop names, with the status that `gandr run`
//! exits with.
//!
//! The run stage makes each [`Evaluation`] (`evaluate`). The script, the
//! type table and the package read them, so these types stay below the run
//! stage. The table of the classes and their statuses is the run stage's.

use alloc::string::String;
use core::fmt;

use anodized::spec;
use gandr_core_sequent::FocusRefusal;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::Stuck;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Declined;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_pretty::Presentation;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a reached hole has no site to report.
    pub mod hole_site {
        /// The hole is not one the program's sources write at one place.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Holes of several sources bear its name.
            Shared,
            /// No computation of the program's sources writes it.
            Unwritten,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a program names no declaration at a position.
    pub mod declaration_name {
        /// The position holds no declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The program declares fewer names.
            Undeclared,
        }
    }
}

/// A value, spelled: the text `gandr run` prints for a run that returned one,
/// laid out by the printer every face shares.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ValueSpelling(Presentation);

impl ValueSpelling
{
    /// The spelling that `presentation` lays out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(presentation: Presentation) -> Self
    {
        Self(presentation)
    }

    /// The presentation the spelling is: its text, whether it says the whole
    /// of the value, and why any `?` in it stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn presentation(&self) -> &Presentation
    {
        &self.0
    }
}

impl AsRef<str> for ValueSpelling
{
    /// The spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_ref()
    }
}

impl fmt::Display for ValueSpelling
{
    /// Writes the spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_ref())
    }
}

/// A run whose value names a member its module's signature hides: the module
/// it is opaque at and the declared type of the declaration run.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SealedRun
{
    /// The path of the module whose signature hides the member.
    module: String,
    /// The declared type of the declaration run, spelled on one line.
    declared: String,
}

impl SealedRun
{
    /// The run opaque at `module`, of the declared type `declared`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(
        module: String,
        declared: String,
    ) -> Self
    {
        Self { module, declared }
    }

    /// The path of the module whose signature hides the member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn module(&self) -> &String
    {
        &self.module
    }

    /// The declared type of the declaration run, spelled on one line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn declared(&self) -> &String
    {
        &self.declared
    }
}

impl fmt::Display for SealedRun
{
    /// Writes `⟨opaque at M⟩ : T`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "⟨opaque at {}⟩ : {}", self.module, self.declared)
    }
}

/// What running one declaration came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evaluation<'source>
{
    /// The run returned a value, or a function: its spelling.
    Value(ValueSpelling),
    /// The run returned a value naming a member its module's signature hides:
    /// opaque at that module.
    Sealed(SealedRun),
    /// The run reached the named declaration, owed its body.
    Blamed(SurfaceName<'source>),
    /// The run reached a hole its source writes, and stopped there.
    Holed
    {
        /// The hole reached.
        hole: HoleId,
        /// Where the source writes it, when one hole of the program bears
        /// its name.
        at: Maybe<ByteSpan, hole_site::Absent>,
    },
    /// The run stopped short of a value.
    Stuck(Stuck),
    /// The run could not be finished.
    Unfinished(Unfinished),
    /// The declaration never reached a run.
    Unrunnable(Unrunnable<'source>),
}

/// Why a run could not be finished.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unfinished
{
    /// The run gave no outcome: its budget ran out, a region passed its
    /// bound, or the lowering refused a form.
    Declined(Declined),
    /// The run's terminal has no reading in the core.
    Readback(ReadbackRefusal),
    /// The run carried as itself a constant the program defines, which the
    /// program's own definitions rule out.
    Inconsistent(ConstantIndex),
    /// The printer could not lay the run's terminal out within its build
    /// ceilings.
    Unspelled,
}

/// Why a declaration never reached the machine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unrunnable<'source>
{
    /// A datatype declaration has no executable body.
    Data(SurfaceName<'source>),
    /// No declaration of the program sits at the position asked for.
    Undeclared(ConstantIndex),
    /// The declaration, or one it refers to, was refused.
    Refused(SurfaceName<'source>),
    /// The declaration, or one it refers to, did not focus: a code, which the
    /// machine carries no image of, or a refusal of the focusing itself.
    Unfocused
    {
        /// The declaration whose body did not focus.
        declaration: SurfaceName<'source>,
        /// Why.
        refusal: FocusRefusal,
    },
    /// No world binding of the host names this world, which the entry holds
    /// a capability for: nothing ran, and nothing was sent.
    UnboundWorld(SurfaceName<'source>),
}

/// How a run went, as `gandr run`'s exit reports it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunStatus
{
    /// The run returned a value.
    Value,
    /// The run reached the machine and stopped short of a value: blamed,
    /// stuck or unfinished.
    Failed,
    /// The source never reached the machine.
    Unreached,
}

impl Evaluation<'_>
{
    /// How the run went, as `gandr run`'s exit reports it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a value, a sealed one among them, is [`RunStatus::Value`]; a
    ///   blamed, holed, stuck or unfinished run [`RunStatus::Failed`]; an
    ///   unrunnable declaration [`RunStatus::Unreached`].
    /// - provides: the one classification the driver's exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run of each class the fragment can write, each
    ///   asserted at its exact status.
    /// - witness: `evaluate::tests::each_outcome_class_has_its_status`
    #[spec(ensures: |ret| match *self {
        Self::Value(_) | Self::Sealed(_) => matches!(ret, RunStatus::Value),
        Self::Blamed(_) | Self::Holed { .. } | Self::Stuck(_) | Self::Unfinished(_) => matches!(ret, RunStatus::Failed),
        Self::Unrunnable(_) => matches!(ret, RunStatus::Unreached),
    })]
    #[inline]
    #[must_use]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            Self::Value(_) | Self::Sealed(_) => RunStatus::Value,
            Self::Blamed(_) | Self::Holed { .. } | Self::Stuck(_) | Self::Unfinished(_) => {
                RunStatus::Failed
            },
            Self::Unrunnable(_) => RunStatus::Unreached,
        }
    }
}

impl fmt::Display for Evaluation<'_>
{
    /// Writes the outcome's one spelling: a value as itself, every other
    /// outcome as its class and what it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: values retain their spelling, a sealed one as `⟨opaque at M⟩
    ///   : T`; other outcomes identify their class and the declaration,
    ///   position or machine reason they carry.
    /// - fails: propagates the formatter's error.
    /// - panics: none.
    /// - executable: none — a formatter exposes neither its destination nor
    ///   written bytes, and its result does not contain the rendered fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value spellings, goal names and distinct numeric
    ///   admission positions retain their roles; a sink failure is not
    ///   injected.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::terminal_classification_preserves_declaration_identity`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unrunnable(Unrunnable::Data(declaration)) => {
                write!(f, "unrunnable: `{declaration}` is a datatype declaration")
            },
            Self::Value(ref value) => fmt::Display::fmt(value, f),
            Self::Sealed(ref sealed) => fmt::Display::fmt(sealed, f),
            Self::Blamed(goal) => write!(f, "blame: `{goal}` is owed its body"),
            Self::Holed { .. } => f.write_str("reached a hole"),
            Self::Stuck(ref stuck) => write!(f, "stuck: {stuck}"),
            Self::Unfinished(Unfinished::Declined(declined)) => write!(f, "unfinished: {declined}"),
            Self::Unfinished(Unfinished::Readback(refusal)) => {
                write!(f, "unfinished: {refusal}")
            },
            Self::Unfinished(Unfinished::Inconsistent(constant)) => write!(
                f,
                "unfinished: the run carried defined constant {} as itself",
                usize::from(constant)
            ),
            Self::Unfinished(Unfinished::Unspelled) => {
                f.write_str("unfinished: the value is too large to spell")
            },
            Self::Unrunnable(Unrunnable::Undeclared(constant)) => write!(
                f,
                "unrunnable: no declaration sits at admission position {}",
                usize::from(constant)
            ),
            Self::Unrunnable(Unrunnable::Refused(declaration)) => {
                write!(f, "unrunnable: `{declaration}` was refused")
            },
            Self::Unrunnable(Unrunnable::Unfocused {
                declaration,
                refusal: FocusRefusal::Code(_),
            }) => write!(
                f,
                "unrunnable: `{declaration}` is a static code, which the machine carries no image of"
            ),
            Self::Unrunnable(Unrunnable::Unfocused {
                declaration,
                refusal,
            }) => write!(f, "unrunnable: `{declaration}` did not focus: {refusal}"),
            Self::Unrunnable(Unrunnable::UnboundWorld(world)) => write!(
                f,
                "unrunnable: UnboundWorld: no world binding names a host for `{world}`, which \
                 the entry may migrate to; nothing was sent"
            ),
        }
    }
}
