//! The run stage: a checked module focused into the command IL, one
//! declaration run — on emitted native code or the portable executor — and
//! its terminal read back and spelled.
//!
//! # A program is its declarations
//!
//! A program is the module's declarations, each a constant the machine
//! unfolds on demand, the source's run target among them. An accepted
//! declaration's elaborated body is focused once, when the program is built; a
//! declaration owed its body, refused, or whose body does not focus is carried
//! as itself, the machine's opaque constant. `gandr run` runs the program's
//! entry, the `main` its source declares at the top level; a source that
//! declares none runs its run target, or the last name it declares when it
//! writes none. The session and the corpus run any accepted declaration by its
//! admission position.
//!
//! # Running a declaration
//!
//! A declaration is a value. Running it returns that value, and when the value
//! is a thunk — a computation suspended, a function's body among them — the
//! thunk is forced, so `def main = thunk { return 42 }` runs to `42` and a
//! function runs to its own terminal, `fn (a) { a }`. The run's terminal is
//! read back into the core and spelled by `gandr-surface-pretty`, the printer
//! a hover answers with; the spelling is the one `gandr run` prints, the
//! session's value line carries and a `runs` expectation compares.
//!
//! **The value spelling is the shared printer's.** A run's value is the
//! computation the printer presents: constructors by their declared names,
//! constants by their paths, a function as its `fn`, a thunk as its body, a
//! tuple as `#{a, b}`, an injection as `+{.0 = v}` and a record as `#{.l =
//! v}` — the grammar's own spellings, laid out on one line. The focused
//! command IL carries a data constructor's family when the core names one,
//! so the read-back value names its constructors. The alternative was the
//! run stage's own renderer, which wrote `ctor[i](…)` and `<fun>` and so
//! answered differently from a hover over the same value; the choice
//! reverses only if a run's value needs a spelling the grammar cannot write.
//!
//! **A run that names a hidden member is opaque at its seal.** A module
//! matched against a signature keeps every member outside the signature out
//! of its interface, so a normal form that mentions one — `SetoidCat.ident(a)`
//! under `SetoidCat : Model(CatShape)` — has no spelling a reader outside the
//! module can write. Such a run is [`Evaluation::Sealed`], reported
//! `⟨opaque at M⟩ : T`: the module whose signature hides the first hidden
//! member the read-back mentions, and the declared type of the declaration
//! run. The report is never a source spelling, so nothing reads it back; the
//! certificate is unchanged. The alternative was to print the hidden member's
//! path, which no source outside the module resolves. The choice reverses if
//! a signature can export a member's spelling without its definition.
//!
//! # Classification
//!
//! A run that returns a value succeeds. A run that reaches a declaration owed
//! its body — returning it, forcing it, applying it or matching on it — is
//! blamed on that declaration, the obligation it met; any other stop short of
//! a value is stuck; a run that could not finish, its jump budget spent, a
//! region exhausted or a form the lowering refuses, is unfinished. Each of
//! these reached the machine. A declaration that did not focus, or that
//! refers, directly or through others, to one that was refused or to a code
//! never reaches it: the reference is found by walking the program's
//! references before any command runs. A referenced declaration whose body
//! did not focus is carried opaque, as an owed one is: a run that reaches it
//! is unrunnable, naming it, and a run that never does — the laws an
//! equivalence carries beside the maps a transport applies — runs to its
//! value.
//!
//! # The run stage follows the check
//!
//! `judge` builds the `Program` from the checker's verdicts, before the kernel
//! is offered anything: nothing the program holds is read from the readmission.
//! Each declaration the checker accepted has its body focused into the command
//! IL by `gandr-core-sequent` and is held as a transparent definition; a
//! declaration owed its body is held opaque, and a refused one, and a code — a
//! type, of which the machine carries no image — are held as the reason they do
//! not run. `Program::evaluate` mints `return c` for the declaration at `c`,
//! runs it on the tier `gandr-runtime-emitter`'s policy picks — emitted
//! native code by default where the host has a patcher, the portable
//! executor elsewhere, both under a budget of 2²⁴ jumps — forces the
//! terminal when it is a thunk, so a suspended computation runs and a
//! function answers its `fn`, and reads the terminal back into the core.
//! `Program::evaluate_on` runs one engine alone, so a differential holds
//! native code to the executor.
//! Nothing runs that no caller asked for: the settle comparison runs the
//! declarations that state a `runs` outcome, the session runs what the user
//! entered, and `gandr run` runs one declaration. The alternative was a run
//! pipeline of its own that composed the source again, which lowers twice and
//! could judge differently from the `check` it follows; the choice reverses if
//! building the program shows on the check path's measurements, when it would
//! move behind a request.
//!
//! **A tier's decline is unfinished.** A tier answers with the evaluation
//! or declines, and a decline is [`Unfinished::Declined`] naming why. The
//! alternative, a second interpreter taking what a tier declines, kept two
//! implementations of one transition table that only tests held together;
//! every corpus `runs` form lowers. The choice reverses if a form the
//! lowering cannot take reaches a `runs` item, when the lowering grows it.
//!
//! | What the run came to | `RunStatus` | `gandr run` exits |
//! | -------------------- | ----------- | ----------------- |
//! | `Evaluation::Value`: a value, spelled; `Evaluation::Sealed`: a value naming a member its module hides, opaque at that module | `Value` | `0` |
//! | `Evaluation::Blamed`: the run reached a declaration owed its body — returned it outside any suspension, forced, applied or matched it | `Failed` | `1` |
//! | `Evaluation::Stuck`, `Evaluation::Unfinished`: any other stop short of a value; the budget spent, the store refusing, a terminal with no reading | `Failed` | `1` |
//! | `Evaluation::Unrunnable`: the declaration, or one it refers to, was refused or is a code | `Unreached` | `2` |
//! | `Ran::Refused`, `Ran::NoProgram`: a declaration of the source was refused, or it declares no name | `Unreached` | `2` |
//!
//! The three statuses are the script contract: `0` for a value, `1` for blame
//! or a stuck configuration, `2` for a source that never reached the machine. A
//! source holding any refusal — the lowering's, the checker's or its root's —
//! does not run even when the target never refers to the refused declaration; a
//! goal is no refusal, and a run that reaches one is blamed on it. Unrunnable
//! references are found by walking the program's references before any command
//! runs, so a run never starts that would meet a declaration the machine cannot
//! carry.
//!
//! **The run target is the source's final expression.** An expression written
//! as a source's last root form is lowered as the body of a thunk and admitted
//! after every name the source declares, so it holds the highest admission
//! position. A source that writes no final expression runs the last name it
//! declares, and a source declaring no name and writing no expression is
//! `Ran::NoProgram`.
//!
//! # Native universe-path boundaries
//!
//! Programmatic native `Path_U` declarations use ordinary checker export and
//! kernel readmission; their portable evidence remains part of the artifact.
//! The command IL runs a native path as the pair of its two maps and a
//! transport along it as the forward map, by the rows `gandr-core-sequent`'s
//! focusing states; a transport whose motive no row reads does not focus and
//! is reported by its head. The printer spells a native path value and an
//! unreduced transport as the core holds them, without executing evidence
//! while printing them. Dependency discovery traverses native classifiers,
//! maps and product components.
//!
//! **Choice.** Keep admission, evaluation and presentation as separate
//! observations. A path accepted by the kernel runs only where focusing has a
//! row for it. **Reversal.** A motive the machine refuses gains a run with
//! its focusing row; no parser syntax or coercion from `Flow_U` is implied
//! here.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::ops::Range;

use anodized::spec;
use gandr_core_checker::Judged;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Verdict;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::FocusRefusal;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_definition;
use gandr_core_sequent::read_back_terminal;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;
use gandr_runtime_emitter::evaluate_on_with_host;
use gandr_runtime_emitter::evaluate_with_host;
use gandr_surface_corpus::RunSpelling;
use gandr_surface_corpus::Runner;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_computation_line;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

mod console;
mod entry;
mod hole;

pub use console::Captured;
pub use console::Console;
pub use console::Line;
pub use console::Printed;
pub use entry::Entered;
pub use entry::Entry;
pub use entry::ExitStatus;
pub use entry::program_entry;
pub use hole::hole_site;

quenchant_shape::reason_enum! {
    /// Why a program has no run target.
    pub mod run_target {
        /// The program declares nothing to run.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source declares no name.
            NoDeclaration,
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

quenchant_shape::reason_enum! {
    /// Why a walk over a run found nothing the machine cannot carry.
    mod carried {
        /// Everything the walk reached is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every declaration or value the walk reached the machine
            /// carries as it is.
            Carried,
        }
    }
}

/// The code-word jumps one run may spend: far past any run the fragment can
/// write, whose only recursion descends structurally and so always halts,
/// and the bound that keeps a run of a later fragment from looping
/// unobserved.
const RUN_BUDGET: usize = 1_usize << 24_u32;

/// The engine a run takes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Engine
{
    /// Code the emitter copies and patches, where the host has a patcher.
    Native,
    /// The portable executor dispatching the same stencils.
    Executor,
}

impl Engine
{
    /// The emitter's tier the engine runs on.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of values, functions, thunks, a text and
    ///   applications runs on each engine as the policy runs it.
    /// - witness: `evaluate::tests::every_engine_spells_a_run_alike`
    const fn tier(self) -> Tier
    {
        match self {
            Self::Native => Tier::Native,
            Self::Executor => Tier::Executor,
        }
    }
}

/// Which tier a run asks the emitter for.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Choice
{
    /// The tier the process's policy picks.
    Policy,
    /// One tier.
    Tier(Tier),
}

/// A checked module, focused and ready to run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program<'source>
{
    /// Every focused definition, and each command minted to run one.
    arena: CommandArena,
    /// What each constant unfolds to, by admission position.
    definitions: Definitions,
    /// Each declaration's name and standing, by admission position; a
    /// position no declaration holds is absent.
    declarations: BTreeMap<ConstantIndex, Declared<'source>>,
    /// The name the printer writes for each constant, by admission position.
    names: Vec<String>,
    /// The path of the module whose signature hides each hidden member, by
    /// the member's admission position.
    hidden: BTreeMap<ConstantIndex, String>,
    /// The declared type, spelled on one line in each spelling, of each
    /// declaration whose run can reach a hidden member, by admission position
    /// and spelling.
    sealed: BTreeMap<(ConstantIndex, Spelling), String>,
    /// The constructors of the module's data declarations, by family.
    families: Families,
    /// The spelling its values and sealed types are written in.
    spelling: Spelling,
    /// The `main` the source run declares at its top level, when it declares
    /// one at an entry's type.
    entry: Maybe<Entry, program_entry::Absent>,
    /// Where the program's sources write each hole an entry run can reach.
    holes: BTreeMap<HoleId, Maybe<ByteSpan, hole_site::Absent>>,
    /// The admission positions of the declarations the source run writes,
    /// among which its run target is chosen: every position, unless the
    /// source is laid after others in its unit.
    own: Range<ConstantIndex>,
}

/// The part of a program a module's leading declarations make: each of them
/// focused, with the sealed type of each whose run reaches a hidden member.
/// A program over a module they lead continues it ([`Program::after`]).
///
/// # Specification
/// - executable: none — a data type; [`Program::after`] states what continuing
///   it answers.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Program::after`].
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[derive(Clone, Debug, Default)]
pub struct Focused<'source>
{
    /// Every focused definition.
    arena: CommandArena,
    /// What each constant unfolds to, by admission position.
    definitions: Definitions,
    /// Each declaration's name and standing, by admission position.
    declarations: BTreeMap<ConstantIndex, Declared<'source>>,
    /// The sealed declared types, by admission position and spelling.
    sealed: BTreeMap<(ConstantIndex, Spelling), String>,
}

/// One declaration of a program: its name and how it stands for a run.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Declared<'source>
{
    /// The declared name.
    name: SurfaceName<'source>,
    /// How the declaration stands for a run.
    slot: Slot,
}

/// How one declaration stands for a run.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Slot
{
    /// Its body focused; the constants the body refers to.
    Defined(Vec<ConstantIndex>),
    /// The checker refused it and its lowered body focused: it runs only as
    /// the root of a refused run, and any other run reaching it stops there as
    /// at a refusal; the constants the body refers to.
    Refused(Vec<ConstantIndex>),
    /// The machine carries it as itself, for the reason given.
    Opaque(Opacity),
}

/// Why the machine carries a declaration as itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opacity
{
    /// A native datatype declares constructors, not an executable value.
    Data,
    /// It is owed its body, or waits on holes that are: running into it is
    /// blame.
    Owed,
    /// It was refused, by the lowering or the checker with no body that
    /// focuses, or the checker accepted it and recorded no body: there is
    /// nothing to run.
    Refused,
    /// Its body did not focus.
    Unfocused(FocusRefusal),
}

/// Which declaration a run may start from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Start
{
    /// A declaration the checker accepted: one it refused stops the run
    /// wherever it is reached.
    Accepted,
    /// The declaration at the root, though the checker refused it: its body
    /// and its references to itself run, and any other refused declaration
    /// stops the run.
    Refused,
}

/// What a run starting from a declaration computes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The declaration's value, forced when it is a suspension.
    Value,
    /// The causal web the dialogue the declaration holds decomposes to:
    /// `decompose` applied to it.
    Web,
}

/// A value, spelled: the text `gandr run` prints for a run that returned one,
/// laid out by the printer every face shares.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ValueSpelling(Presentation);

impl ValueSpelling
{
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

/// Where a run of a declaration ended: its terminal value read back, or the
/// evaluation that ended it before there was one to read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Terminal<'source>
{
    /// The terminal value, read back as the computation returning it into
    /// the arena the run was given.
    Read(ComputationId),
    /// The evaluation the run ended with first: unrunnable, stuck, blamed, or
    /// a terminal whose read-back refused.
    Ended(Evaluation<'source>),
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
        }
    }
}

impl<'source> Program<'source>
{
    /// The program `module` and its verdicts describe, its accepted bodies
    /// read out of `core`.
    ///
    /// # Specification
    /// - requires: `verdicts` are the checker's report for `module`, judged
    ///   over `core`; the module's admission positions ascend and may skip a
    ///   position no declaration holds.
    /// - ensures: one entry per declaration of `module`, at its own admission
    ///   position, so a reference a body holds reads the declaration it names.
    ///   A declaration checked or synthesised has its elaborated body focused
    ///   and is defined as it; one owed its body is carried as itself; one the
    ///   checker refused has its lowered body focused, run only as the root of
    ///   [`Self::evaluate_refused`]; one refused by the lowering, or by the
    ///   checker with no body that focuses, or whose body does not focus, is
    ///   carried as itself and never run. A skipped position holds no
    ///   declaration and an opaque definition; a position met again keeps its
    ///   first declaration. Each member a module matched against a signature
    ///   keeps out of its interface is hidden at that module's path, and each
    ///   declaration whose references reach a hidden member, transitively,
    ///   holds its declared type spelled on one line, in each spelling, where
    ///   the printer can lay it out. Its values are spelled in
    ///   [`Spelling::Unicode`].
    /// - provides: the program every run of the module's declarations shares.
    /// - fails: never; a body that does not focus is the declaration's
    ///   standing, not a failure of the program.
    /// - panics: none.
    /// - intension: one focusing per accepted or checker-refused declaration;
    ///   nothing runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sources holding an accepted, an owed, a refused and
    ///   an unfocusable declaration are built and each run asserted at its
    ///   exact outcome. A module whose positions skip one keeps every
    ///   declaration at its admission position, a later body's reference to an
    ///   earlier one runs, and the skipped position is undeclared.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::a_skipped_admission_position_holds_no_declaration`
    #[spec(
        ensures: |ref ret| ret.spelling == Spelling::Unicode && usize::from(ret.definitions.len())
                == module.declarations().iter().map(|lowered| usize::from(lowered.constant()).saturating_add(1)).max().unwrap_or(0)
            && ret.declarations.keys().all(|constant| module.declarations().iter().any(|lowered| lowered.constant() == *constant))
            && module.declarations().iter().all(|lowered| ret.declarations.get(&lowered.constant()).is_some_and(|declared|
                module.declarations().iter().find(|first| first.constant() == lowered.constant()).is_some_and(|first| declared.name == first.name())))
            && (0..usize::from(ret.definitions.len())).all(|position| {
                let constant = ConstantIndex::from(position);
                match (ret.definitions.get(constant), ret.declarations.get(&constant).map(|declared| &declared.slot)) {
                    (Some(Definition::Transparent(producer)), Some(&(Slot::Defined(_) | Slot::Refused(_)))) => ret.arena.producer(producer).is_some(),
                    (Some(Definition::Opaque), Some(&Slot::Opaque(_)) | None) => true,
                    _ => false,
                }
            })
    )]
    #[must_use]
    pub(crate) fn new(
        core: &CoreArena,
        module: &LoweredModule<'source>,
        verdicts: &ModuleReport,
    ) -> Self
    {
        Self::after(Focused::default(), core, module, verdicts)
    }

    /// [`Self::new`] continuing `focused`, the part of the program the
    /// module's leading declarations make: its declarations are taken as
    /// focused and sealed, and only the later ones are focused and spelled.
    ///
    /// # Specification
    /// - requires: as [`Self::new`]; `focused` is [`Self::into_focused`] of the
    ///   program of a module whose declarations lead `module`'s, judged over an
    ///   arena `core` extends, its verdicts leading `verdicts`.
    /// - ensures: the program [`Self::new`] builds of `module`.
    /// - provides: a document's program at the cost of its own declarations.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause is [`Self::new`]'s answer over the whole
    ///   module; the witness compares the two.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document judged after a closure judged once
    ///   composes, its program included, as on a fresh judgement of the
    ///   closure; a position no declaration takes is skipped; a run naming a
    ///   hidden member reads the declared type the program sealed. Widening the
    ///   sealed filter to a declaration before `focused`'s boundary or one
    ///   reaching no hidden member changes no run: the first was sealed by the
    ///   leading program in the same spelling, and only a run whose read-back
    ///   mentions a hidden member reads the seal, which such a declaration's
    ///   run never does.
    /// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_skipped_admission_position_holds_no_declaration`
    /// - witness: `evaluate::tests::a_run_naming_a_hidden_member_is_opaque_at_its_module`
    #[must_use]
    #[cfg_attr(feature = "hotpath", hotpath::measure)]
    pub(crate) fn after(
        focused: Focused<'source>,
        core: &CoreArena,
        module: &LoweredModule<'source>,
        verdicts: &ModuleReport,
    ) -> Self
    {
        let Focused {
            mut arena,
            mut definitions,
            mut declarations,
            mut sealed,
        } = focused;
        // Focusing only records each command's origin, which no program
        // keeps, so a continued focusing starts an empty table.
        let mut provenance = Provenance::new();
        let boundary = usize::from(definitions.len());
        let mut judged = verdicts.judged().iter().peekable();
        for lowered in module.declarations() {
            let constant = lowered.constant();
            let verdict = judged
                .next_if(|answer| answer.constant() == constant)
                .map(Judged::verdict);
            if usize::from(constant) < usize::from(definitions.len()) {
                continue;
            }
            let body = verdicts.definitions().get(&constant).copied();
            let (definition, slot) = match (verdict, body) {
                (Some(Verdict::Data), _) => (Definition::Opaque, Slot::Opaque(Opacity::Data)),
                (Some(Verdict::Checked { .. } | Verdict::Synthesised { .. }), Some(body)) => {
                    match focus_definition(core, body, &mut arena, &mut provenance) {
                        Ok(producer) => (
                            Definition::Transparent(producer),
                            Slot::Defined(references(core, body)),
                        ),
                        Err(refusal) => (
                            Definition::Opaque,
                            Slot::Opaque(Opacity::Unfocused(refusal)),
                        ),
                    }
                },
                (Some(Verdict::Owed(_) | Verdict::Suspended(_)), _) => {
                    (Definition::Opaque, Slot::Opaque(Opacity::Owed))
                },
                (Some(Verdict::Refused(_)), _) => match lowered.outcome() {
                    DeclarationOutcome::Completed { body, .. }
                    | DeclarationOutcome::Bodied { body } => {
                        focus_definition(core, body, &mut arena, &mut provenance).map_or(
                            (Definition::Opaque, Slot::Opaque(Opacity::Refused)),
                            |producer| {
                                (
                                    Definition::Transparent(producer),
                                    Slot::Refused(references(core, body)),
                                )
                            },
                        )
                    },
                    DeclarationOutcome::Uncompleted { .. }
                    | DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Codata(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World
                    | DeclarationOutcome::Refused(_) => {
                        (Definition::Opaque, Slot::Opaque(Opacity::Refused))
                    },
                },
                (Some(Verdict::Checked { .. } | Verdict::Synthesised { .. }) | None, _) => {
                    (Definition::Opaque, Slot::Opaque(Opacity::Refused))
                },
            };
            while usize::from(definitions.len()) < usize::from(constant) {
                let _skipped = definitions.push(Definition::Opaque);
            }
            let _position = definitions.push(definition);
            let _fresh = declarations.insert(constant, Declared {
                name: lowered.name(),
                slot,
            });
        }
        let names = constant_names(module);
        // A run's value is read back into an arena of its own, whose cases
        // the module's would misname.
        let families = Families::declared(module);
        let hidden = hidden_members(module);
        if !hidden.is_empty() {
            let reaching = reaching(&declarations, &hidden);
            let printed: Vec<Name<'_>> =
                names.iter().map(|name| Name::from(name.as_str())).collect();
            let constructors = families.naming(&printed);
            let source = CoreSource::new(core, &printed).naming(&constructors);
            // A leading declaration's references, and the members it can
            // reach, are the leading module's, so its type was spelled
            // there.
            sealed.extend(
                verdicts
                    .judged()
                    .iter()
                    .filter(|judged| {
                        usize::from(judged.constant()) >= boundary
                            && reaching.contains(&judged.constant())
                    })
                    .filter_map(|judged| match judged.verdict() {
                        Verdict::Checked { declared, .. } | Verdict::Suspended(declared) => {
                            Some((judged.constant(), declared.id()))
                        },
                        Verdict::Synthesised { synthesised, .. } => {
                            Some((judged.constant(), synthesised.produced().id()))
                        },
                        Verdict::Data | Verdict::Owed(_) | Verdict::Refused(_) => None,
                    })
                    .flat_map(|(constant, declared)| {
                        [Spelling::Unicode, Spelling::Ascii]
                            .map(|spelling| ((constant, spelling), declared))
                    })
                    .filter_map(|((constant, spelling), declared)| {
                        present_type(
                            &source,
                            CoreNode::ValueType(declared),
                            PageWidth::from(u32::from(u16::MAX)),
                            Style {
                                form: Form::Sugared,
                                spelling,
                            },
                        )
                        .ok()
                        .map(|spelled| ((constant, spelling), spelled.to_string()))
                    }),
            );
        }
        Self {
            arena,
            definitions,
            declarations,
            names,
            hidden,
            sealed,
            families,
            spelling: Spelling::Unicode,
            entry: entry::entry_of(core, module, verdicts),
            holes: hole::hole_sites(core, module),
            own: ConstantIndex::from(0_usize) .. ConstantIndex::from(usize::MAX),
        }
    }

    /// The part of this program a module laid after its module continues
    /// ([`Self::after`]): its focused declarations and sealed types.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn into_focused(self) -> Focused<'source>
    {
        let Self {
            arena,
            definitions,
            declarations,
            sealed,
            ..
        } = self;
        Focused {
            arena,
            definitions,
            declarations,
            sealed,
        }
    }

    /// This program, its values and sealed types written in `spelling`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later run spells its value, or its sealed type, in
    ///   `spelling`; what runs is unchanged.
    /// - provides: the reader's spelling for `gandr run` and the session; a
    ///   `runs` expectation is compared in the program's own spelling, Unicode,
    ///   before any face asks for another.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value holding a relation runs to its spelling in
    ///   each spelling.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling_in_either_spelling_782`
    #[spec(ensures: self.spelling == spelling)]
    #[inline]
    pub fn spell_in(
        &mut self,
        spelling: Spelling,
    )
    {
        self.spelling = spelling;
    }

    /// This program, run as the source whose declarations stand at the
    /// admission positions `own`.
    ///
    /// # Specification
    /// - requires: `own` holds exactly the positions of the declarations the
    ///   source writes.
    /// - ensures: [`Self::target`] reads only the declarations at `own`;
    ///   nothing else changes.
    /// - provides: a source laid after the prelude and its imports runs its own
    ///   last declaration, never theirs.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the store is a move; [`Self::target`] states what
    ///   it changes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a script declaring nothing, laid after the prelude,
    ///   has no program.
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    pub(crate) fn run_within(
        &mut self,
        own: Range<ConstantIndex>,
    )
    {
        self.own = own;
    }

    /// The declaration `gandr run` runs: the source's run target, or the last
    /// name the source declares when it writes none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the highest admission position among the source's own
    ///   ([`Self::run_within`]), which is the source's run target, admitted
    ///   after every name, when it writes one, and otherwise the name the
    ///   source declared last for the first time.
    /// - provides: the declaration a source runs.
    /// - fails: [`run_target::Absent::NoDeclaration`] when the source declares
    ///   no name and writes no run target.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of several names, a later declaration of an
    ///   earlier name among them, a source of none, a final expression after a
    ///   name and after a later declaration of an earlier name, and a source of
    ///   none laid after the prelude.
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    /// - witness: `evaluate::tests::a_final_expression_is_the_run_target_1105`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(last) => self.own.contains(&last) && self.declarations.contains_key(&last),
        Maybe::Absent(run_target::Absent::NoDeclaration) => true,
    })]
    #[inline]
    pub fn target(&self) -> Maybe<ConstantIndex, run_target::Absent>
    {
        match self.declarations.range(self.own.clone()).next_back() {
            Some((&last, _)) => Maybe::Present(last),
            None => Maybe::Absent(run_target::Absent::NoDeclaration),
        }
    }

    /// The name of the declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing; any admission position may be queried.
    /// - ensures: the name stored at the exact position, or `Undeclared` when
    ///   no declaration holds the position, without truncating the index.
    /// - fails: an absent name is the typed absence, never a substitute name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct names retain their positions across a later
    ///   definition of an earlier name; empty and maximal-index queries are
    ///   absent.
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    #[spec(ensures: |ret| match (self.declarations.get(&constant), ret) {
        (Some(declared), Maybe::Present(name)) => declared.name == name,
        (None, Maybe::Absent(declaration_name::Absent::Undeclared)) => true,
        _ => false,
    })]
    #[inline]
    pub fn name(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<SurfaceName<'source>, declaration_name::Absent>
    {
        self.declarations.get(&constant).map_or(
            Maybe::Absent(declaration_name::Absent::Undeclared),
            |declared| Maybe::Present(declared.name),
        )
    }

    /// Each declaration whose accepted body did not focus, with the focusing's
    /// refusal, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the declarations whose bodies failed focusing, with
    ///   their own names and refusals, in admission order; other slots are
    ///   absent.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — anodized rejects postconditions on this opaque
    ///   iterator return type with E0562; observing the sequence requires
    ///   instrumentation support rather than changing the public signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four codes, three of them reached through references,
    ///   are never listed, and the one transport the machine does not lower is;
    ///   other focusing refusal kinds are not generated.
    /// - witness: `evaluate::tests::a_code_and_every_reference_to_it_run_to_the_type_it_quotes`
    #[inline]
    pub fn focus_refusals(&self)
    -> impl Iterator<Item = (SurfaceName<'source>, FocusRefusal)> + '_
    {
        self.declarations
            .values()
            .filter_map(|declared| match declared.slot {
                Slot::Opaque(Opacity::Unfocused(refusal)) => Some((declared.name, refusal)),
                Slot::Defined(_)
                | Slot::Refused(_)
                | Slot::Opaque(Opacity::Data | Opacity::Owed | Opacity::Refused) => None,
            })
    }

    /// Run the declaration at `constant`, read its terminal back and spell it.
    ///
    /// # Specification
    /// - requires: nothing; a position the program does not hold is an outcome
    ///   of its own.
    /// - ensures: [`Unrunnable`] when the position holds no declaration, or the
    ///   declaration or one it refers to, transitively, was refused or did not
    ///   focus, decided before any command runs. Otherwise the declaration runs
    ///   on the tier the emitter's policy picks — emitted native code by
    ///   default where the host has a patcher, the portable executor elsewhere
    ///   — and its value is returned, forced when it is a thunk; a terminal
    ///   that is, or holds outside any suspension, a declaration owed its body,
    ///   and a run stuck observing one, is [`Evaluation::Blamed`] on it; any
    ///   other stuck run is [`Evaluation::Stuck`]; a run the tier declines, a
    ///   terminal with no core reading or one the printer cannot lay out is
    ///   [`Evaluation::Unfinished`]; otherwise the terminal is read back and
    ///   spelled as the grammar writes it: an integer in decimal, a text quoted
    ///   with its escapes, `unit`, a tuple as `#{a, b}`, an injection as `+{.i
    ///   = v}`, a constructor by its name, a thunk as `thunk { … }` and a
    ///   function as its `fn`; a read-back terminal that mentions a member its
    ///   module's signature hides is instead [`Evaluation::Sealed`] at that
    ///   module with the declared type of the declaration run, or
    ///   [`Unfinished::Unspelled`] when that type has no layout.
    /// - provides: the run stage every caller shares, so one declaration has
    ///   one outcome and one spelling wherever it is run.
    /// - fails: never; every failure is an outcome. A refused entry command
    ///   also produces `Unrunnable`; its attempted focusing may already have
    ///   appended command-arena nodes.
    /// - panics: none.
    /// - intension: each run is bounded by a jump budget; the reference walk,
    ///   the readback and the spelling are recursion-free, their pending work
    ///   explicit stacks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one source per outcome class the fragment can write
    ///   and per spelling arm it can reach, each run asserted at its exact
    ///   evaluation; a goal met directly, through a force and through an
    ///   application; a refused and a code reference reached directly and
    ///   through another declaration. Exhaustion and every core spelling
    ///   constructor are not generated by the source cases; structured
    ///   terminals have separate core-to-store and spelling witnesses.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::each_outcome_class_has_its_status`
    /// - witness: `evaluate::tests::a_constructed_terminal_blames_its_first_opaque_field`
    /// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
    /// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
    /// - witness: `evaluate::tests::every_engine_spells_a_run_alike`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body's reachability walk marks every declaration; the check scans the declarations once for the reported name"
        )
    )]
    #[spec(
        captures: [declarations = self.declarations.len(), definitions = self.definitions.len(),
            watermark = self.arena.watermark(), blocked = match self.declarations.get(&constant) {
                None => Some(Unrunnable::Undeclared(constant)),
                Some(&Declared {name,slot:Slot::Opaque(Opacity::Data)}) => Some(Unrunnable::Data(name)),
                Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) | Slot::Refused(_) }) => Some(Unrunnable::Refused(name)),
                Some(&Declared { name, slot: Slot::Opaque(Opacity::Unfocused(refusal)) }) =>
                    Some(Unrunnable::Unfocused { declaration: name, refusal }),
                Some(&Declared { slot: Slot::Defined(_) | Slot::Opaque(Opacity::Owed), .. }) => None,
            }],
        ensures: |ref ret| self.declarations.len() == declarations && self.definitions.len() == definitions
            && blocked.is_none_or(|reason| matches!(*ret, Evaluation::Unrunnable(actual) if actual == reason)
                && self.arena.watermark() == watermark)
            && match *ret {
                Evaluation::Unrunnable(Unrunnable::Data(name)) => self.declarations.values().any(|declared| declared.name == name && matches!(declared.slot,Slot::Opaque(Opacity::Data))),
                Evaluation::Blamed(name) => self.declarations.values().any(|declared|
                    declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Owed))),
                Evaluation::Unrunnable(Unrunnable::Undeclared(index)) => !self.declarations.contains_key(&index),
                Evaluation::Unrunnable(Unrunnable::Refused(name)) => self.declarations.values().any(|declared|
                    declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Refused) | Slot::Refused(_))),
                Evaluation::Unrunnable(Unrunnable::Unfocused { declaration, .. }) =>
                    self.declarations.values().any(|declared| declared.name == declaration),
                Evaluation::Unfinished(Unfinished::Inconsistent(index)) => self.declarations.get(&index)
                    .is_some_and(|declared| matches!(declared.slot, Slot::Defined(_))),
                Evaluation::Sealed(ref sealed) => self.hidden.values().any(|module| *module == sealed.module)
                    && self.sealed.get(&(constant, self.spelling)).is_some_and(|declared| *declared == sealed.declared),
                Evaluation::Holed { hole, at } => self.holes.get(&hole).is_some_and(|site| *site == at)
                    || (matches!(at, Maybe::Absent(hole_site::Absent::Unwritten)) && !self.holes.contains_key(&hole)),
                Evaluation::Value(_) | Evaluation::Stuck(_)
                    | Evaluation::Unfinished(Unfinished::Declined(_) | Unfinished::Readback(_) | Unfinished::Unspelled) => true,
            }
    )]
    #[inline]
    pub fn evaluate(
        &mut self,
        constant: ConstantIndex,
    ) -> Evaluation<'source>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return evaluation,
        };
        self.tiered(constant, returned, forced, Choice::Policy, None)
            .unwrap_or_else(|declined| Evaluation::Unfinished(Unfinished::Declined(declined)))
    }

    /// Run the declaration at `constant` as [`Self::evaluate`] does, each line
    /// it prints handed to `console`.
    ///
    /// # Specification
    /// - requires: nothing; a position the program does not hold is an outcome
    ///   of its own.
    /// - ensures: what [`Self::evaluate`] gives, but a `Console.print` the run
    ///   performs and no handler of its own claims writes its line to
    ///   `console`, in order, and resumes with the unit, where
    ///   [`Self::evaluate`] leaves the run stuck at it.
    /// - provides: `gandr run`'s run of a source's target, and a `runs`
    ///   expectation's run under a capturing console.
    /// - fails: never; every failure is an outcome.
    /// - panics: none.
    /// - executable: none — the run's clauses are [`Self::evaluate`]'s.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration printing a line runs to its value with
    ///   the line captured, and its `runs` expectation states both.
    /// - witness: `evaluate::tests::a_printed_line_reaches_the_console_2279`
    #[inline]
    pub fn evaluate_printing(
        &mut self,
        constant: ConstantIndex,
        console: &mut dyn Console,
    ) -> Evaluation<'source>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return evaluation,
        };
        self.tiered(constant, returned, forced, Choice::Policy, Some(console))
            .unwrap_or_else(|declined| Evaluation::Unfinished(Unfinished::Declined(declined)))
    }

    /// Run the declaration at `constant` though the checker refused it, read
    /// its terminal back and spell it.
    ///
    /// # Specification
    /// - requires: nothing; a position the program does not hold is an outcome
    ///   of its own.
    /// - ensures: what [`Self::evaluate`] gives, but for a declaration the
    ///   checker refused whose lowered body focused: that body runs as an
    ///   accepted one would, its references to itself included, and any other
    ///   refused declaration it reaches is [`Unrunnable::Refused`], decided
    ///   before any command runs.
    /// - provides: the run a `runs` beside a `refuses` compares, so a refusal's
    ///   witness can also state what the refused program does.
    /// - fails: never; every failure is an outcome.
    /// - panics: none.
    /// - executable: none — the walk's clauses are [`Self::unrunnable`]'s and
    ///   the run's [`Self::evaluate`]'s; agreeing with them is the witnesses'.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration runs to its value, one reaching
    ///   another refused declaration stays unrunnable, and the strict run of
    ///   the same declaration still refuses it.
    /// - witness: `evaluate::tests::a_refused_declaration_runs_only_as_its_own_root`
    #[inline]
    pub fn evaluate_refused(
        &mut self,
        constant: ConstantIndex,
    ) -> Evaluation<'source>
    {
        let (returned, forced) = match self.prepare(constant, Start::Refused, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return evaluation,
        };
        self.tiered(constant, returned, forced, Choice::Policy, None)
            .unwrap_or_else(|declined| Evaluation::Unfinished(Unfinished::Declined(declined)))
    }

    /// Run `decompose` over the dialogue the declaration at `constant`
    /// holds, read the web back and spell it.
    ///
    /// # Specification
    /// - requires: nothing; a position the program does not hold is an outcome
    ///   of its own.
    /// - ensures: what [`Self::evaluate`] gives for a declaration applying
    ///   `decompose` to the one at `constant`: the web's spelling, or the
    ///   outcome that stops the run short of one, a declaration whose value is
    ///   no dialogue included.
    /// - provides: the run a `decomposes` expectation compares.
    /// - fails: never; every failure is an outcome.
    /// - panics: none.
    /// - executable: none — the run's clauses are [`Self::evaluate`]'s.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus's series-parallel dialogue and the one
    ///   leaving a prime node settle only when this spells the webs `decompose`
    ///   returns for them.
    /// - witness: `tests::corpus::the_fixture_root_settles_every_fixture`
    #[inline]
    pub fn evaluate_decomposed(
        &mut self,
        constant: ConstantIndex,
    ) -> Evaluation<'source>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Web) {
            Ok(entries) => entries,
            Err(evaluation) => return evaluation,
        };
        self.tiered(constant, returned, forced, Choice::Policy, None)
            .unwrap_or_else(|declined| Evaluation::Unfinished(Unfinished::Declined(declined)))
    }

    /// Run the declaration at `constant` on `engine` alone, declining rather
    /// than spelling a decline as unfinished.
    ///
    /// # Specification
    /// - ensures: the [`Evaluation::Unrunnable`] outcomes [`Self::evaluate`]
    ///   gives, before any engine runs; an engine that answers gives the
    ///   evaluation [`Self::evaluate`] gives on it.
    /// - provides: the engines apart, so a differential holds native code to
    ///   the executor and counts what either declines.
    /// - panics: none.
    /// - executable: none — agreeing across engines is the differential's to
    ///   show; a postcondition would run every evaluation twice.
    ///
    /// # Errors
    /// [`Declined`] naming why the engine did not answer: a form the lowering
    /// refuses, an exhausted budget or region.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — one source of values, functions, thunks, a text and
    ///   applications runs on every engine, and native code answers as the
    ///   executor does.
    /// - witness: `evaluate::tests::every_engine_spells_a_run_alike`
    #[inline]
    pub fn evaluate_on(
        &mut self,
        constant: ConstantIndex,
        engine: Engine,
    ) -> Result<Evaluation<'source>, Declined>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return Ok(evaluation),
        };
        self.tiered(
            constant,
            returned,
            forced,
            Choice::Tier(engine.tier()),
            None,
        )
    }

    /// Run the declaration at `constant` on `engine` alone, as
    /// [`Self::evaluate_on`] does, each line it prints handed to `console`.
    ///
    /// # Specification
    /// - ensures: what [`Self::evaluate_on`] gives, but a `Console.print` the
    ///   run performs writes its line to `console` and resumes with the unit,
    ///   as under [`Self::evaluate_printing`].
    /// - provides: the engines apart under a console, so a differential holds
    ///   each to a `runs` expectation that states printed lines.
    /// - panics: none.
    /// - executable: none — as [`Self::evaluate_on`].
    ///
    /// # Errors
    /// As [`Self::evaluate_on`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration printing two lines runs on the executor
    ///   as under [`Self::evaluate_printing`].
    /// - witness: `evaluate::tests::a_printed_line_reaches_the_console_2279`
    #[inline]
    pub fn evaluate_printing_on(
        &mut self,
        constant: ConstantIndex,
        engine: Engine,
        console: &mut dyn Console,
    ) -> Result<Evaluation<'source>, Declined>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return Ok(evaluation),
        };
        self.tiered(
            constant,
            returned,
            forced,
            Choice::Tier(engine.tier()),
            Some(console),
        )
    }

    /// Run the declaration at `constant` on `engine` alone, as
    /// [`Self::evaluate_on`] does, and read its terminal value back into
    /// `into` instead of spelling it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`Evaluation::Unrunnable`] [`Self::evaluate_on`] gives
    ///   before any engine runs, and the evaluation a run that blames or sticks
    ///   ends with, as [`Terminal::Ended`]; otherwise the run's terminal value,
    ///   forced when it is a suspension, read back as a computation of `into`,
    ///   or [`Unfinished::Readback`] when it does not read back. A run reaching
    ///   a member its module's signature hides is read back like any other.
    /// - provides: the run as a core term, so a differential holds it to
    ///   another evaluator's normal form node for node.
    /// - panics: none.
    /// - executable: none — the read-back term is the clause, and holding it to
    ///   the normaliser is the differential's.
    ///
    /// # Errors
    /// [`Declined`], as [`Self::evaluate_on`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every `runs` item of the corpus reads back on the
    ///   executor to the normaliser's answer.
    /// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
    #[inline]
    pub fn read_on(
        &mut self,
        constant: ConstantIndex,
        engine: Engine,
        into: &mut CoreArena,
    ) -> Result<Terminal<'source>, Declined>
    {
        let (returned, forced) = match self.prepare(constant, Start::Accepted, Reach::Value) {
            Ok(entries) => entries,
            Err(evaluation) => return Ok(Terminal::Ended(evaluation)),
        };
        let mut store = Store::new();
        Ok(
            match self.terminal(
                (returned, forced),
                Choice::Tier(engine.tier()),
                (&mut store, None),
            )? {
                Ok(terminal) => match read_back_terminal(&self.arena, &store, terminal, into) {
                    Ok(read) => Terminal::Read(read),
                    Err(refusal) => {
                        Terminal::Ended(Evaluation::Unfinished(Unfinished::Readback(refusal)))
                    },
                },
                Err(evaluation) => Terminal::Ended(evaluation),
            },
        )
    }

    /// The two commands that run the declaration at `constant` to `reach`,
    /// started as `start` allows: the one returning it and the one forcing
    /// it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The [`Evaluation::Unrunnable`] that blocks the run.
    fn prepare(
        &mut self,
        constant: ConstantIndex,
        start: Start,
        reach: Reach,
    ) -> Result<(CommandId, CommandId), Evaluation<'source>>
    {
        if let Maybe::Present(unrunnable) = self.unrunnable(constant, start) {
            return Err(Evaluation::Unrunnable(unrunnable));
        }
        self.entries(constant, reach).map_err(|refusal| {
            Evaluation::Unrunnable(match self.name(constant) {
                Maybe::Present(declaration) => Unrunnable::Unfocused {
                    declaration,
                    refusal,
                },
                Maybe::Absent(declaration_name::Absent::Undeclared) => {
                    Unrunnable::Undeclared(constant)
                },
            })
        })
    }

    /// Run the commands on a tier the choice names, forcing a suspended
    /// answer, and spell the terminal; or blame the opaque constant a run
    /// observed or answers outside any suspension.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The tier's [`Declined`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values, a text, functions, thunks and applications
    ///   each run to their pinned spelling.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    fn tiered(
        &self,
        constant: ConstantIndex,
        returned: CommandId,
        forced: CommandId,
        choice: Choice,
        console: Option<&mut dyn Console>,
    ) -> Result<Evaluation<'source>, Declined>
    {
        let mut store = Store::new();
        Ok(
            match self.terminal((returned, forced), choice, (&mut store, console))? {
                Ok(terminal) => self.finish(constant, &store, terminal),
                Err(evaluation) => evaluation,
            },
        )
    }

    /// Run the commands on a tier the choice names into `store`, forcing a
    /// suspended answer: the terminal value, or the evaluation that ends the
    /// run first, blaming the opaque constant it observed or answers outside
    /// any suspension. With a console, each `Console.print` the run offers its
    /// host writes its line there and resumes; without one it stops the run.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The tier's [`Declined`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::tiered`], and a terminal read back as a
    ///   core term is the normaliser's answer.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `tests::differential::a_transport_along_an_inline_equivalence_normalises_1677`
    fn terminal(
        &self,
        (returned, forced): (CommandId, CommandId),
        choice: Choice,
        (store, mut console): (&mut Store, Option<&mut dyn Console>),
    ) -> Result<Result<HeapValueId, Evaluation<'source>>, Declined>
    {
        let fuel = Fuel::from(RUN_BUDGET);
        let mut run = |root, store: &mut Store| {
            let Some(ref mut console) = console
            else {
                return match choice {
                    Choice::Policy => gandr_runtime_emitter::evaluate(
                        &self.arena,
                        &self.definitions,
                        root,
                        fuel,
                        store,
                    ),
                    Choice::Tier(tier) => {
                        evaluate_on(tier, &self.arena, &self.definitions, root, fuel, store)
                    },
                };
            };
            let mut host = console::PrintingHost::new(&mut **console);
            let hosted = match choice {
                Choice::Policy => evaluate_with_host(
                    &self.arena,
                    &self.definitions,
                    root,
                    (fuel, store),
                    &mut host,
                ),
                Choice::Tier(tier) => evaluate_on_with_host(
                    tier,
                    (&self.arena, &self.definitions, root),
                    (fuel, store),
                    &mut host,
                ),
            }?;
            Ok(match hosted {
                HostOutcome::Completed(outcome) => outcome,
                HostOutcome::Aborted(never) => match never {},
            })
        };
        let outcome = run(returned, store)?;
        let terminal = match self.halted(store, outcome) {
            Ok(terminal) => terminal,
            Err(evaluation) => return Ok(Err(evaluation)),
        };
        Ok(match store.value(terminal) {
            Some(&(HeapValue::Thunk { .. } | HeapValue::Fixpoint { .. })) => {
                let outcome = run(forced, store)?;
                self.halted(store, outcome)
            },
            Some(
                &(HeapValue::Literal(_)
                | HeapValue::Code(_)
                | HeapValue::Constructed { .. }
                | HeapValue::Stack { .. }
                | HeapValue::Closure { .. }
                | HeapValue::Opaque(_)
                | HeapValue::Capability),
            )
            | None => Ok(terminal),
        })
    }

    /// Read the terminal `terminal` of `store` back and spell it, or name the
    /// module whose signature it reaches past.
    ///
    /// # Specification
    /// trivial.
    fn finish(
        &self,
        constant: ConstantIndex,
        store: &Store,
        terminal: HeapValueId,
    ) -> Evaluation<'source>
    {
        let mut core = CoreArena::new();
        match read_back_terminal(&self.arena, store, terminal, &mut core) {
            Ok(read) => match self.hidden_in(&mut core, read) {
                Maybe::Present(module) => self.sealed.get(&(constant, self.spelling)).map_or(
                    Evaluation::Unfinished(Unfinished::Unspelled),
                    |declared| {
                        Evaluation::Sealed(SealedRun {
                            module: module.clone(),
                            declared: declared.clone(),
                        })
                    },
                ),
                Maybe::Absent(carried::Absent::Carried) => self
                    .spell(&core, read)
                    .map_or_else(Evaluation::Unfinished, Evaluation::Value),
            },
            Err(refusal) => Evaluation::Unfinished(Unfinished::Readback(refusal)),
        }
    }

    /// The module whose signature hides the first hidden member the read-back
    /// terminal `read` mentions, outside its types.
    ///
    /// # Specification
    /// - requires: `read` was read back into `core`.
    /// - ensures: the path of the module hiding the first constant, in the
    ///   reference walk's order, that a module's signature hides; carried when
    ///   the terminal mentions none, or when no module hides a member, without
    ///   walking the terminal.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one reference walk over the terminal, wrapped in a thunk
    ///   appended to the scratch arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function whose body applies a member its module's
    ///   signature hides, and runs naming only exported members of a sealed
    ///   module.
    /// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
    #[spec(ensures: |ret| !self.hidden.is_empty() || matches!(ret, Maybe::Absent(carried::Absent::Carried)))]
    fn hidden_in(
        &self,
        core: &mut CoreArena,
        read: ComputationId,
    ) -> Maybe<&String, carried::Absent>
    {
        if self.hidden.is_empty() {
            return Maybe::Absent(carried::Absent::Carried);
        }
        let terminal = core.value_thunk(read);
        references(core, terminal)
            .into_iter()
            .find_map(|constant| self.hidden.get(&constant))
            .map_or(Maybe::Absent(carried::Absent::Carried), Maybe::Present)
    }

    /// The first declaration reachable from `constant` through references
    /// that the machine cannot carry, as the reason it never runs, the run
    /// started as `start` allows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` itself when it did not focus, else the first
    ///   reached absent, refused or code declaration, with its exact identity;
    ///   an owed declaration, and a referenced one whose body did not focus, is
    ///   carried. A checker-refused declaration whose body focused is carried
    ///   only as the root of a [`Start::Refused`] run, each reference back to
    ///   it included. Absence means the reachable reference graph contains no
    ///   such obstacle.
    /// - fails: an undeclared reference reports its own index, not the run
    ///   target.
    /// - panics: none.
    /// - intension: each declared position is expanded at most once, including
    ///   when references repeat or form a cycle.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct and transitive refusal and code references are
    ///   blocked, while owed references and the laws of an equivalence reach
    ///   the machine; cycles are not built by these admitted source fixtures.
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_body_that_did_not_focus_is_carried_until_reached`
    /// - witness: `evaluate::tests::a_refused_declaration_runs_only_as_its_own_root`
    /// - witness: `evaluate::tests::a_run_reaching_a_static_code_is_blocked_by_it`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body marks each declaration its walk reaches; the check scans the declarations once for the reported name"
        )
    )]
    #[spec(ensures: |ret| {
        let root = match self.declarations.get(&constant) {
            None => ret == Maybe::Present(Unrunnable::Undeclared(constant)),
            Some(&Declared {name,slot:Slot::Opaque(Opacity::Data)}) => ret == Maybe::Present(Unrunnable::Data(name)),
            Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) }) => ret == Maybe::Present(Unrunnable::Refused(name)),
            Some(&Declared { name, slot: Slot::Refused(_) }) => start == Start::Refused || ret == Maybe::Present(Unrunnable::Refused(name)),
            Some(&Declared { name, slot: Slot::Opaque(Opacity::Unfocused(refusal)) }) =>
                ret == Maybe::Present(Unrunnable::Unfocused { declaration: name, refusal }),
            Some(&Declared { slot: Slot::Opaque(Opacity::Owed), .. }) => matches!(ret, Maybe::Absent(carried::Absent::Carried)),
            Some(&Declared { slot: Slot::Defined(_), .. }) => true,
        };
        root && match ret {
            Maybe::Present(Unrunnable::Data(name)) => self.declarations.values().any(|declared| declared.name == name && matches!(declared.slot,Slot::Opaque(Opacity::Data))),
            Maybe::Present(Unrunnable::Undeclared(index)) => !self.declarations.contains_key(&index),
            Maybe::Present(Unrunnable::Refused(name)) => self.declarations.values().any(|declared|
                declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Refused) | Slot::Refused(_))),
            Maybe::Present(Unrunnable::Unfocused { declaration, refusal }) => self.declarations.values().any(|declared|
                declared.name == declaration && matches!(declared.slot, Slot::Opaque(Opacity::Unfocused(actual)) if actual == refusal)),
            Maybe::Absent(carried::Absent::Carried) => true,
        }
    })]
    fn unrunnable(
        &self,
        constant: ConstantIndex,
        start: Start,
    ) -> Maybe<Unrunnable<'source>, carried::Absent>
    {
        let mut seen = BTreeSet::new();
        let mut pending = Vec::from([constant]);
        while let Some(reached) = pending.pop() {
            let Some(declared) = self.declarations.get(&reached)
            else {
                return Maybe::Present(Unrunnable::Undeclared(reached));
            };
            if !seen.insert(reached) {
                continue;
            }
            match declared.slot {
                Slot::Opaque(Opacity::Data) => {
                    return Maybe::Present(Unrunnable::Data(declared.name));
                },
                Slot::Defined(ref referred) => pending.extend(referred.iter().copied()),
                Slot::Refused(ref referred) => {
                    if reached != constant || start == Start::Accepted {
                        return Maybe::Present(Unrunnable::Refused(declared.name));
                    }
                    pending.extend(referred.iter().copied());
                },
                Slot::Opaque(Opacity::Owed) => {},
                Slot::Opaque(Opacity::Refused) => {
                    return Maybe::Present(Unrunnable::Refused(declared.name));
                },
                // A body outside the command IL is carried opaque until a run
                // reaches it; a code is a type, a value of which no run holds.
                Slot::Opaque(Opacity::Unfocused(refusal)) => {
                    if reached == constant || matches!(refusal, FocusRefusal::Code(_)) {
                        return Maybe::Present(Unrunnable::Unfocused {
                            declaration: declared.name,
                            refusal,
                        });
                    }
                },
            }
        }
        Maybe::Absent(carried::Absent::Carried)
    }

    /// The two commands a run of `constant` to `reach` needs: for its value,
    /// `return c`, and `force c` for a constant whose value is a thunk; for
    /// its web, `decompose(c)` for both, a web being no thunk.
    ///
    /// # Specification
    /// - requires: nothing; the constant need not have a definition yet.
    /// - ensures: success returns allocated commands for the same constant in
    ///   this program's arena: distinct return and force commands, in that
    ///   order, for its value, and one decompose command twice for its web.
    /// - fails: preserves the focusing refusal; nodes already appended are not
    ///   rolled back when a later allocation fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordinary value runs through the return entry and a
    ///   thunk through both entries; allocation exhaustion is not forced.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    #[spec(ensures: |ret| match ret {
        Ok((returned, forced)) => (returned != forced) == (reach == Reach::Value)
            && self.arena.command(returned).is_some()
            && self.arena.command(forced).is_some(),
        Err(_) => true,
    })]
    /// # Errors
    /// The [`FocusRefusal`] of a command arena that refused a node.
    fn entries(
        &mut self,
        constant: ConstantIndex,
        reach: Reach,
    ) -> Result<(CommandId, CommandId), FocusRefusal>
    {
        let mut core = CoreArena::new();
        let value = core.value_constant(constant);
        let mut provenance = Provenance::new();
        match reach {
            Reach::Value => {
                let returned = core.computation_return(value);
                let forced = core.computation_force(value);
                Ok((
                    focus_computation(&core, returned, &mut self.arena, &mut provenance)?,
                    focus_computation(&core, forced, &mut self.arena, &mut provenance)?,
                ))
            },
            Reach::Web => {
                let decomposed = core.computation_decompose(value);
                let web = focus_computation(&core, decomposed, &mut self.arena, &mut provenance)?;
                Ok((web, web))
            },
        }
    }

    /// The value `outcome` halted with, or the evaluation it ends the run
    /// with: blame on a declaration owed its body met at the terminal or by an
    /// observation, and the stuck state otherwise.
    ///
    /// # Specification
    /// - requires: `outcome` was moved into `store` by a run; a halted id
    ///   resolves there.
    /// - ensures: success returns the identical halted id, never an immediately
    ///   opaque value. A run stuck at the perform focusing leaves for a hole is
    ///   [`Evaluation::Holed`] with that hole and its site; any other stuck
    ///   result retains its precise stuck reason; opacity reached outside
    ///   suspension is instead classified by declaration standing.
    /// - fails: returns blame, unrunnability or inconsistency for an opaque
    ///   declaration, the reached hole, or the unchanged stuck outcome; it
    ///   never spells a value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct, forced and applied goals preserve blame,
    ///   while a constructed terminal selects its first opaque field and an
    ///   unforced suspension does not expose its goal; other stuck reasons are
    ///   not separately generated by these source and core fixtures.
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_constructed_terminal_blames_its_first_opaque_field`
    /// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
    #[spec(
        requires: match outcome { Outcome::Halted(value) => store.value(value).is_some(), Outcome::Stuck(_) => true },
        captures: [halted = match outcome { Outcome::Halted(value) => Some(value), Outcome::Stuck(_) => None },
            stuck = match outcome { Outcome::Stuck(ref reason) => Some(core::mem::discriminant(reason)), Outcome::Halted(_) => None },
            unhandled = matches!(outcome, Outcome::Stuck(Stuck::PerformNoHandler(_)))],
        ensures: |ref ret| match *ret {
            Ok(value) => halted == Some(value)
                && !matches!(store.value(value), Some(&HeapValue::Opaque(_))),
            Err(Evaluation::Stuck(ref actual)) => stuck == Some(core::mem::discriminant(actual)),
            Err(Evaluation::Holed { .. }) => unhandled,
            Err(Evaluation::Value(_) | Evaluation::Sealed(_)) => false,
            Err(Evaluation::Blamed(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_)) => true,
        }
    )]
    /// # Errors
    /// The evaluation a run ends with when it halted on, or stuck at, an
    /// opaque constant, or stuck otherwise.
    fn halted(
        &self,
        store: &Store,
        outcome: Outcome,
    ) -> Result<HeapValueId, Evaluation<'source>>
    {
        match outcome {
            Outcome::Halted(value) => match Self::opaque_within(store, value) {
                Maybe::Present(constant) => Err(self.met(constant)),
                Maybe::Absent(carried::Absent::Carried) => Ok(value),
            },
            Outcome::Stuck(Stuck::PerformNoHandler(at))
                if let Maybe::Present(hole) = hole::reached(&self.arena, at) =>
            {
                Err(Evaluation::Holed {
                    hole,
                    at: self
                        .holes
                        .get(&hole)
                        .copied()
                        .unwrap_or(Maybe::Absent(hole_site::Absent::Unwritten)),
                })
            },
            Outcome::Stuck(stuck) => {
                let observed = match stuck {
                    Stuck::Unobservable { value, .. }
                    | Stuck::ResumedNonStack { value, .. }
                    | Stuck::Unmatched { value, .. }
                    | Stuck::NonScalar(value) => store.value(value),
                    Stuck::PerformNoHandler(_)
                    | Stuck::ShiftNoReset(_)
                    | Stuck::Primitive(_)
                    | Stuck::UndefinedConstant(_)
                    | Stuck::CyclicConstant(_)
                    | Stuck::Unended(_)
                    | Stuck::Outside(_) => None,
                };
                match observed {
                    Some(&HeapValue::Opaque(constant)) => Err(self.met(constant)),
                    Some(
                        &(HeapValue::Literal(_)
                        | HeapValue::Code(_)
                        | HeapValue::Constructed { .. }
                        | HeapValue::Stack { .. }
                        | HeapValue::Thunk { .. }
                        | HeapValue::Fixpoint { .. }
                        | HeapValue::Closure { .. }
                        | HeapValue::Capability),
                    )
                    | None => Err(Evaluation::Stuck(stuck)),
                }
            },
        }
    }

    /// The first opaque constant `value` holds outside any suspension.
    ///
    /// # Specification
    /// - requires: the reachable constructed-value graph is finite and acyclic.
    ///   A missing id is permitted and ignored.
    /// - ensures: the first opaque field in left-to-right depth-first order is
    ///   returned; literals, missing values and suspensions contribute none. A
    ///   thunk or closure is never entered merely to look for blame.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested fields distinguish field order from admission
    ///   order; a goal underneath an unforced thunk remains unobserved.
    /// - witness: `evaluate::tests::a_constructed_terminal_blames_its_first_opaque_field`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    #[spec(ensures: |ret| match store.value(value) {
        Some(&HeapValue::Opaque(constant)) => ret == Maybe::Present(constant),
        Some(&HeapValue::Constructed { .. }) => true,
        Some(&(HeapValue::Stack { .. } | HeapValue::Literal(_) | HeapValue::Code(_) | HeapValue::Thunk { .. } | HeapValue::Fixpoint { .. } | HeapValue::Closure { .. } | HeapValue::Capability)) | None =>
            matches!(ret, Maybe::Absent(carried::Absent::Carried)),
    })]
    fn opaque_within(
        store: &Store,
        value: HeapValueId,
    ) -> Maybe<ConstantIndex, carried::Absent>
    {
        let mut pending = Vec::from([value]);
        while let Some(id) = pending.pop() {
            match store.value(id) {
                Some(&HeapValue::Opaque(constant)) => return Maybe::Present(constant),
                Some(&HeapValue::Constructed { ref fields, .. }) => {
                    pending.extend(fields.iter().rev().copied());
                },
                Some(
                    &(HeapValue::Stack { .. }
                    | HeapValue::Literal(_)
                    | HeapValue::Code(_)
                    | HeapValue::Thunk { .. }
                    | HeapValue::Fixpoint { .. }
                    | HeapValue::Closure { .. }
                    | HeapValue::Capability),
                )
                | None => {},
            }
        }
        Maybe::Absent(carried::Absent::Carried)
    }

    /// The evaluation of a run that met the opaque constant `constant`.
    ///
    /// # Specification
    /// - requires: nothing; missing and even defined positions are classified.
    /// - ensures: owed positions blame their name, refused and unfocused ones —
    ///   a checker-refused one whose body focused included — remain unrunnable
    ///   with their identity, a defined position is inconsistent, and an absent
    ///   position reports that exact undeclared index.
    /// - fails: every classification is an evaluation, never a panic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real composed declarations exercise every standing,
    ///   including the inconsistent defined and out-of-range boundaries.
    /// - witness: `evaluate::tests::terminal_classification_preserves_declaration_identity`
    #[spec(ensures: |ref ret| match self.declarations.get(&constant) {
        Some(&Declared {name,slot:Slot::Opaque(Opacity::Data)}) => matches!(*ret,Evaluation::Unrunnable(Unrunnable::Data(actual)) if actual == name),
        Some(&Declared { name, slot: Slot::Opaque(Opacity::Owed) }) => matches!(*ret, Evaluation::Blamed(actual) if actual == name),
        Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) | Slot::Refused(_) }) => matches!(*ret, Evaluation::Unrunnable(Unrunnable::Refused(actual)) if actual == name),
        Some(&Declared { name, slot: Slot::Opaque(Opacity::Unfocused(refusal)) }) => matches!(*ret,
            Evaluation::Unrunnable(Unrunnable::Unfocused { declaration, refusal: actual }) if declaration == name && actual == refusal),
        Some(&Declared { slot: Slot::Defined(_), .. }) => matches!(*ret, Evaluation::Unfinished(Unfinished::Inconsistent(actual)) if actual == constant),
        None => matches!(*ret, Evaluation::Unrunnable(Unrunnable::Undeclared(actual)) if actual == constant),
    })]
    fn met(
        &self,
        constant: ConstantIndex,
    ) -> Evaluation<'source>
    {
        match self.declarations.get(&constant) {
            Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Data),
            }) => Evaluation::Unrunnable(Unrunnable::Data(name)),
            Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Owed),
            }) => Evaluation::Blamed(name),
            Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Refused) | Slot::Refused(_),
            }) => Evaluation::Unrunnable(Unrunnable::Refused(name)),
            Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Unfocused(refusal)),
            }) => Evaluation::Unrunnable(Unrunnable::Unfocused {
                declaration: name,
                refusal,
            }),
            Some(&Declared {
                slot: Slot::Defined(_),
                ..
            }) => Evaluation::Unfinished(Unfinished::Inconsistent(constant)),
            None => Evaluation::Unrunnable(Unrunnable::Undeclared(constant)),
        }
    }

    /// The spelling of the terminal `read`, read back into `core`, through
    /// the printer every face shares.
    ///
    /// # Specification
    /// - requires: nothing; a malformed core graph is admissible.
    /// - ensures: the terminal presented as the computation it is, in the
    ///   sugared form and the program's spelling on one line without a break
    ///   search: a returned value as the value, a function as its `fn`,
    ///   constants by their paths from the top level and constructors by their
    ///   names, every former as the grammar writes it and `?` where the printer
    ///   cannot spell a node; the unspelled-layout absence where the printer
    ///   cannot write it.
    /// - provides: the one value spelling `gandr run`, the session and a `runs`
    ///   expectation share, the same printer a hover answers with.
    /// - fails: [`Unfinished::Unspelled`] when the presentation reaches a build
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source values cover integers, text, unit, functions,
    ///   thunks, constructors, tuples and injections at their exact spellings;
    ///   the corpus `runs` expectations pin every value the corpus runs to.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref spelled) => !AsRef::<str>::as_ref(spelled).is_empty(),
        Err(ref unfinished) => *unfinished == Unfinished::Unspelled,
    })]
    fn spell(
        &self,
        core: &CoreArena,
        read: ComputationId,
    ) -> Result<ValueSpelling, Unfinished>
    {
        let names: Vec<Name<'_>> = self
            .names
            .iter()
            .map(|name| Name::from(name.as_str()))
            .collect();
        let constructors = self.families.naming(&names);
        let source = CoreSource::new(core, &names).naming(&constructors);
        present_computation_line(&source, CoreNode::Computation(read), Style {
            form: Form::Sugared,
            spelling: self.spelling,
        })
        .map(ValueSpelling)
        .map_err(|_refusal| Unfinished::Unspelled)
    }
}

/// Each member a module matched against a signature keeps out of its
/// interface, with that module's path.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every declaration whose container is a module that matching
///   coerced, and whose admission position none of that module's exported value
///   components resolves to, keyed by that position and holding the module's
///   path joined by `.`; a member hidden by two modules keeps the first.
/// - fails: never.
/// - panics: none.
/// - intension: a module no signature coerced is skipped without a walk.
///
/// # Adequacy
/// - hypothesis: L3 — a model whose helpers stand outside its signature, and
///   sealed modules whose runs name only their exports.
/// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
/// - witness: `evaluate::tests::a_run_naming_a_declaration_outside_every_sealed_module_is_spelled`
#[spec(ensures: |ref ret| ret.keys().all(|constant| module.declarations().iter().any(|declaration| declaration.constant() == *constant)))]
fn hidden_members(module: &LoweredModule<'_>) -> BTreeMap<ConstantIndex, String>
{
    let mut hidden = BTreeMap::new();
    let mut exported: BTreeSet<ConstantIndex> = BTreeSet::new();
    let mut at = String::new();
    for structure in module.structures() {
        if !structure.coerced().0 {
            continue;
        }
        exported.clear();
        exported.extend(
            structure
                .values()
                .iter()
                .map(|component| component.constant),
        );
        at.clear();
        for (index, segment) in structure.path().iter().enumerate() {
            if index > 0 {
                at.push('.');
            }
            at.push_str(AsRef::<str>::as_ref(segment));
        }
        for declaration in module.declarations() {
            let path = module.path_of(declaration);
            if path
                .split_last()
                .is_some_and(|(_, container)| container == structure.path())
                && !exported.contains(&declaration.constant())
            {
                let _first = hidden
                    .entry(declaration.constant())
                    .or_insert_with(|| at.clone());
            }
        }
    }
    hidden
}

/// Every declaration whose references reach a member of `hidden`, directly or
/// through other declarations, the hidden members among them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the least set holding every hidden member and every defined
///   declaration one of whose references the set holds.
/// - fails: never.
/// - panics: none.
/// - intension: one pass building each constant's referrers, then a walk over
///   them from the hidden members on an explicit stack, each declaration
///   entered once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`hidden_members`]: a model's interface operations
///   reach its helpers through their bodies.
/// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
#[spec(ensures: |ref ret| hidden.keys().all(|constant| ret.contains(constant)))]
fn reaching(
    declarations: &BTreeMap<ConstantIndex, Declared<'_>>,
    hidden: &BTreeMap<ConstantIndex, String>,
) -> BTreeSet<ConstantIndex>
{
    let mut referrers: BTreeMap<ConstantIndex, Vec<ConstantIndex>> = BTreeMap::new();
    for (&constant, declared) in declarations {
        if let Slot::Defined(ref referred) = declared.slot {
            for &target in referred {
                referrers.entry(target).or_default().push(constant);
            }
        }
    }
    let mut reached: BTreeSet<ConstantIndex> = hidden.keys().copied().collect();
    let mut pending: Vec<ConstantIndex> = reached.iter().copied().collect();
    while let Some(target) = pending.pop() {
        for &referrer in referrers.get(&target).into_iter().flatten() {
            if reached.insert(referrer) {
                pending.push(referrer);
            }
        }
    }
    reached
}

impl Runner for Program<'_>
{
    /// Spells the outcome of running the declaration at `constant` under a
    /// capturing console: each line it printed, each followed by a newline,
    /// then the outcome, as `gandr run` writes them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling
    {
        let mut captured = Captured::default();
        let evaluation = self.evaluate_printing(constant, &mut captured);
        let mut spelled = String::new();
        for line in captured.lines() {
            spelled.push_str(line);
            spelled.push('\n');
        }
        spelled.push_str(&evaluation.to_string());
        RunSpelling::from(spelled)
    }

    /// Spells the outcome of running the declaration at `constant` though
    /// the checker refused it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run_refused(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling
    {
        RunSpelling::from(self.evaluate_refused(constant).to_string())
    }

    /// Spells the web the dialogue the declaration at `constant` holds
    /// decomposes to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn decompose(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling
    {
        RunSpelling::from(self.evaluate_decomposed(constant).to_string())
    }
}

/// The constants `body` refers to, outside its types.
///
/// # Specification
/// - requires: the reachable term graph is finite and acyclic; missing ids are
///   ignored rather than followed.
/// - ensures: one index per reference occurrence, preserving multiplicity;
///   quoted types and static code do not contribute references, and neither
///   does a hole. A constant root contributes only itself and an atomic
///   non-reference root contributes none.
/// - fails: never.
/// - panics: none.
/// - intension: traversal uses an explicit worklist without recursion.
///
/// # Adequacy
/// - hypothesis: L3 — real transitive source references prevent unsafe runs,
///   and a nested core value retains repeated references rather than
///   deduplicating. Every core wrapper is not separately generated.
/// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
/// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
#[spec(ensures: |ref ret| match core.value(body) {
    Some(&Value::Constant(constant)) => ret.iter().copied().eq([constant]),
    Some(&Value::Primitive { .. } |
&(Value::ListNil | Value::Variable { .. } | Value::Literal(_) | Value::Quote(_) |
Value::QuoteComputation(_) | Value::StaticLambda(_) |
Value::StaticApplication(..) | Value::Hole(_) | Value::Web(_) | Value::Row(_))) | None => ret.is_empty(),
    Some(&(Value::Constructor { .. } | Value::Record(_)) |
&Value::Reify(_) |
&Value::Univalence(..) |
&(Value::ListCons(..) | Value::PathRefl(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::RecordUpdate { .. } | Value::PathProduct(..) |
Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Dialogue(_) |
Value::PathEquiv { .. } | Value::Tuple(_) | Value::Injection(..) |
Value::Lift { .. } | Value::Thunk(_) | Value::Mark { .. } | Value::Ascribe { .. })) => true,
})]
fn references(
    core: &CoreArena,
    body: ValueId,
) -> Vec<ConstantIndex>
{
    /// A node still to visit.
    #[derive(Clone, Copy)]
    enum Node
    {
        /// A value.
        Value(ValueId),
        /// A computation.
        Computation(ComputationId),
    }
    let mut referred = Vec::new();
    let mut pending = Vec::from([Node::Value(body)]);
    while let Some(node) = pending.pop() {
        match node {
            Node::Value(id) => {
                match core.value(id) {
                    Some(&Value::Constructor { ref fields, .. }) => {
                        pending.extend(fields.iter().copied().map(Node::Value));
                    },
                    Some(&Value::Record(ref fields)) => {
                        pending.extend(fields.values().copied().map(Node::Value));
                    },
                    Some(&Value::Reify(ref frames)) => {
                        pending.extend(frames.iter().filter_map(|frame| match *frame {
                            gandr_core_term::control::StackFrame::Apply(value) => {
                                Some(Node::Value(value))
                            },
                            gandr_core_term::control::StackFrame::Bind(body) => {
                                Some(Node::Computation(body))
                            },
                            gandr_core_term::control::StackFrame::Project(_) => None,
                        }));
                    },

                    Some(&Value::Constant(constant)) => referred.push(constant),
                    Some(
                        &(Value::PathProduct(first, second)
                        | Value::Funext(first, second)
                        | Value::Equiv(first, second)
                        | Value::Univalence(first, second)
                        | Value::Ua {
                            forward: first,
                            backward: second,
                            ..
                        }
                        | Value::PathEquiv {
                            forward: first,
                            backward: second,
                            ..
                        }
                        | Value::ListCons(first, second)
                        | Value::Then(first, second)
                        | Value::FlowProduct(first, second)
                        | Value::FunctionFlow(first, second)
                        | Value::RecordUpdate {
                            base: first,
                            overlay: second,
                        }),
                    ) => {
                        pending.extend([Node::Value(first), Node::Value(second)]);
                    },
                    Some(&Value::SessionRelated {
                        source,
                        target,
                        payloads,
                        ..
                    }) => {
                        pending.extend([source, target, payloads].map(Node::Value));
                    },
                    Some(&Value::Tuple(ref components)) => {
                        pending.extend(components.iter().map(|&component| Node::Value(component)));
                    },
                    Some(
                        &(Value::PathRefl(inner)
                        | Value::Here(inner)
                        | Value::Stay(inner)
                        | Value::Forward(inner)
                        | Value::Injection(_, inner)
                        | Value::Lift { body: inner, .. }
                        | Value::Mark { body: inner, .. }
                        | Value::Ascribe { value: inner, .. }),
                    ) => {
                        pending.push(Node::Value(inner));
                    },
                    Some(&Value::Recorded(ref moves)) => {
                        pending.extend(moves.iter().filter_map(|step| match step.payload() {
                            Maybe::Present(payload) => Some(Node::Value(payload)),
                            Maybe::Absent(_) => None,
                        }));
                    },
                    Some(&Value::Dialogue(ref moves)) => {
                        pending.extend(moves.iter().filter_map(
                            |turn| match turn.movement.payload() {
                                Maybe::Present(payload) => Some(Node::Value(payload)),
                                Maybe::Absent(_) => None,
                            },
                        ));
                    },
                    Some(
                        &Value::Thunk(computation)
                        | &Value::Returned(computation)
                        | &Value::Nested(computation)
                        | &Value::Run(computation),
                    ) => {
                        pending.push(Node::Computation(computation));
                    },
                    Some(
                        &Value::Primitive { .. }
                        | &(Value::Variable { .. }
                        | Value::ListNil
                        | Value::Literal(_)
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::StaticLambda(_)
                        | Value::StaticApplication(..)
                        | Value::Hole(_)
                        | Value::Web(_)
                        | Value::Row(_)),
                    )
                    | None => {},
                }
            },
            Node::Computation(id) => match core.computation(id) {
                Some(&Computation::DataCase {
                    scrutinee,
                    ref branches,
                    ..
                }) => {
                    pending.push(Node::Value(scrutinee));
                    pending.extend(branches.iter().copied().map(Node::Computation));
                },
                Some(
                    &(Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _)),
                ) => {
                    pending.push(Node::Value(record));
                },
                Some(&Computation::Perform { payload, .. }) => pending.push(Node::Value(payload)),
                Some(
                    &(Computation::Handle {
                        subject,
                        on_return,
                        ref clauses,
                        ..
                    }
                    | Computation::Scope {
                        subject,
                        on_return,
                        ref clauses,
                        ..
                    }),
                ) => {
                    pending.extend([Node::Computation(subject), Node::Computation(on_return)]);
                    pending.extend(clauses.iter().map(|clause| Node::Computation(clause.body)));
                },
                Some(&Computation::Exercise {
                    capability,
                    payload,
                    ..
                }) => pending.extend([Node::Value(capability), Node::Value(payload)]),
                Some(
                    &(Computation::Resume(value, body)
                    | Computation::Split {
                        scrutinee: value,
                        body,
                        ..
                    }),
                ) => {
                    pending.extend([Node::Value(value), Node::Computation(body)]);
                },
                Some(
                    &(Computation::Reset(body)
                    | Computation::Shift(body)
                    | Computation::Project(_, body)
                    | Computation::Ascribe { body, .. }),
                ) => pending.push(Node::Computation(body)),
                Some(&Computation::With(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| Node::Computation(component)),
                    );
                },

                Some(
                    &(Computation::ListFold {
                        list,
                        on_nil,
                        on_cons,
                        ..
                    }
                    | Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    }),
                ) => pending.extend([
                    Node::Value(list),
                    Node::Computation(on_nil),
                    Node::Computation(on_cons),
                ]),
                Some(&Computation::Primitive { ref arguments, .. }) => {
                    pending.extend(arguments.iter().copied().map(Node::Value));
                },
                Some(
                    &(Computation::Transport(path, value)
                    | Computation::PathTransport { path, value, .. }),
                ) => {
                    pending.extend([Node::Value(path), Node::Value(value)]);
                },
                Some(&Computation::Ride { flow, value, .. }) => {
                    pending.extend([Node::Value(flow), Node::Value(value)]);
                },
                Some(&Computation::TelescopeTransport {
                    path,
                    start,
                    over,
                    value,
                    ..
                }) => {
                    pending.extend([path, start, over, value].map(Node::Value));
                },
                Some(&Computation::Lambda(inner)) => pending.push(Node::Computation(inner)),
                Some(&Computation::Application(head, argument)) => {
                    pending.extend([Node::Computation(head), Node::Value(argument)]);
                },
                Some(
                    &(Computation::Return(value)
                    | Computation::Abandon(value)
                    | Computation::Force(value)
                    | Computation::Decompose(value)),
                ) => {
                    pending.push(Node::Value(value));
                },
                Some(&Computation::Bind(bound, rest)) => {
                    pending.extend([Node::Computation(bound), Node::Computation(rest)]);
                },
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push(Node::Value(scrutinee));
                    pending.extend(branches.iter().map(|&branch| Node::Computation(branch)));
                },
                Some(&(Computation::Mark { body, .. } | Computation::Fixpoint { body, .. })) => {
                    pending.push(Node::Computation(body));
                },
                Some(&Computation::Session(ref action)) => {
                    pending.extend(action.values().map(Node::Value));
                    pending.extend(action.computations().map(Node::Computation));
                },
                Some(&Computation::Memory(ref form)) => {
                    pending.extend(form.values().map(Node::Value));
                    pending.extend(form.computations().map(Node::Computation));
                },
                Some(&Computation::World(ref form)) => {
                    pending.extend(form.values().map(Node::Value));
                    pending.extend(form.computations().map(Node::Computation));
                },
                Some(&Computation::Hole(_)) | None => {},
            },
        }
    }
    referred
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_core_sequent::FocusRefusal;
    use gandr_core_sequent::Store;
    use gandr_core_sequent::Stuck;
    use gandr_kernel_term::ConstantIndex;
    use gandr_runtime_emitter::Declined;
    use gandr_runtime_emitter::Fuel;
    use gandr_runtime_emitter::PATCHER;
    use gandr_runtime_emitter::Status;
    use gandr_runtime_emitter::Tier;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Captured;
    use super::Engine;
    use super::Evaluation;
    use super::Program;
    use super::Reach;
    use super::RunStatus;
    use super::SealedRun;
    use super::Spelling;
    use super::Unfinished;
    use super::Unrunnable;
    use super::run_target;
    use crate::compose::Composed;
    use crate::compose::LoweringCount;
    use crate::compose::compose;

    /// The program `source` composes to under the fixture root.
    ///
    /// # Specification
    /// - requires: a flat source fixture that composes without an engine fault
    ///   or whole-module refusal under the fixture root.
    /// - ensures: every declared name stands at a position the definitions
    ///   cover.
    /// - panics: if the grammar or composition premise fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values, goals, refusals, later definitions of
    ///   existing names and an empty source have independent expected outcomes
    ///   or targets.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    #[spec(ensures: |ref ret| ret.declarations.keys().all(|&constant| ret.definitions.get(constant).is_some()))]
    pub(super) fn program<'source>(source: impl Into<SourceText<'source>>) -> Program<'source>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        match compose(&grammar, CorpusRoot::Fixture, source.into(), &mut lowerings) {
            Ok(Composed::Settled { program, .. }) => program,
            Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            Err(fault) => panic!("faulted: {fault}"),
        }
    }

    /// What running the declaration named `name` of `program` comes to.
    ///
    /// # Specification
    /// - requires: `program` declares `name`.
    /// - ensures: evaluates that name without changing declaration count; an
    ///   undeclared-reference result lies outside the program, not at another
    ///   name.
    /// - panics: if the named declaration is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — named values, direct and indirect goals and refused
    ///   references return independent expected evaluations.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "test fixture: the body searches the declarations for the name once; the check searches them once"
        )
    )]
    #[spec(
        requires: program.declarations.values().any(|declared| declared.name == name),
        captures: [declarations = program.declarations.len()],
        ensures: |ref ret| program.declarations.len() == declarations
            && match *ret { Evaluation::Unrunnable(Unrunnable::Undeclared(index)) => !program.declarations.contains_key(&index), Evaluation::Value(_) | Evaluation::Sealed(_) | Evaluation::Blamed(_) | Evaluation::Holed { .. } | Evaluation::Stuck(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_) => true }
    )]
    fn run<'source>(
        program: &mut Program<'source>,
        name: SurfaceName<'source>,
    ) -> Evaluation<'source>
    {
        let position = program
            .declarations
            .iter()
            .find(|&(_, declared)| declared.name == name)
            .map(|(&constant, _)| constant)
            .expect("the program declares the name");
        program.evaluate(position)
    }

    #[test]
    fn a_value_runs_to_its_spelling()
    {
        let mut values = program(
            r#"def answer : Integer ; def answer = 42 ;
def greeting : String ; def greeting = "a \"quoted\"\nline" ;
def nothing : Unit ; def nothing = unit ;
def copy = answer ;
def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { return x } } ;
def first : +U (Integer -> Integer -> -F Integer) ; def first = thunk { fn (x) { fn (y) { return x } } } ;
def applied : +U (-F Integer) ; def applied = thunk { become (force identity)(answer) } ;
def chosen : +U (-F Integer) ; def chosen = thunk { become (force first)(answer)(7) } ;
def delayed : +U (-F String) ; def delayed = thunk { return "later" } ;
def nested : +U (-F (+U (-F Integer))) ; def nested = thunk { return thunk { return 1 } } ;"#,
        );
        for (name, spelled) in [
            ("answer", "42"),
            ("greeting", r#""a \"quoted\"\nline""#),
            ("nothing", "unit"),
            ("copy", "42"),
            ("identity", "fn (a) { a }"),
            ("first", "fn (a) { fn (b) { a } }"),
            ("applied", "42"),
            ("chosen", "42"),
            ("delayed", r#""later""#),
            ("nested", "thunk { 1 }"),
        ] {
            let evaluation = run(&mut values, SurfaceName::from(name));
            assert!(
                matches!(evaluation, Evaluation::Value(_)),
                "`{name}` runs to a value: {evaluation}"
            );
            assert_eq!(
                evaluation.to_string(),
                spelled,
                "`{name}` is spelled as pinned"
            );
        }
    }

    /// A `Console.print` the run performs hands its line to the console and
    /// resumes with the unit, in order; with no console the run is stuck at
    /// the first (#2279).
    #[test]
    fn a_printed_line_reaches_the_console_2279()
    {
        let mut printing = program(
            "def greet() -> -F [Console] Unit {\n  Console.print(\"a\") ;\n  \
             Console.print(\"b\")\n}\n",
        );
        let greet = printing
            .declarations
            .iter()
            .find(|&(_, declared)| declared.name == SurfaceName::from("greet"))
            .map(|(&constant, _)| constant)
            .expect("the program declares `greet`");
        let mut console = Captured::default();
        assert_eq!(
            printing.evaluate_printing(greet, &mut console).to_string(),
            "unit",
            "the run returns the unit"
        );
        assert_eq!(console.lines(), ["a", "b"], "each line, in order");
        let mut executed = Captured::default();
        assert_eq!(
            printing
                .evaluate_printing_on(greet, Engine::Executor, &mut executed)
                .map(|evaluation| evaluation.to_string()),
            Ok(String::from("unit")),
            "the executor alone runs it alike"
        );
        assert_eq!(executed.lines(), ["a", "b"], "and prints alike");
        assert!(
            matches!(printing.evaluate(greet), Evaluation::Stuck(_)),
            "with no console the perform is stuck"
        );
    }

    /// #782: a value is spelled in the program's spelling, Unicode until a
    /// face asks for another.
    #[test]
    fn a_value_runs_to_its_spelling_in_either_spelling_782()
    {
        let mut words = program(
            "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef once : +U (-F \
             Path(Circle, Base, Base)) ; def once = thunk { loop } ;",
        );
        for (spelling, spelled) in [
            (Spelling::Unicode, "loop ∷ here(Base)"),
            (Spelling::Ascii, "loop :: here(Base)"),
        ] {
            words.spell_in(spelling);
            assert_eq!(
                run(&mut words, SurfaceName::from("once")).to_string(),
                spelled,
                "the word in {spelling:?}"
            );
        }
    }

    /// Every engine spells a run as the executor does: values, a text,
    /// functions, thunks and applications answer on native code and under
    /// the policy with the executor's evaluation.
    #[test]
    fn every_engine_spells_a_run_alike()
    {
        let mut values = program(
            r#"def answer : Integer ; def answer = 42 ;
def greeting : String ; def greeting = "words" ;
def nothing : Unit ; def nothing = unit ;
def copy = answer ;
def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { return x } } ;
def first : +U (Integer -> Integer -> -F Integer) ; def first = thunk { fn (x) { fn (y) { return x } } } ;
def applied : +U (-F Integer) ; def applied = thunk { become (force identity)(answer) } ;
def chosen : +U (-F Integer) ; def chosen = thunk { become (force first)(answer)(7) } ;
def nested : +U (-F (+U (-F Integer))) ; def nested = thunk { return thunk { return 1 } } ;
def small : Type ; def small = Integer ;
def same(a : Type, x : a) -> -F a { return x }
def instantiated : +U (-F Integer) ; def instantiated = thunk { become same(Integer, 5) } ;"#,
        );
        let declared: Vec<_> = values.declarations.keys().copied().collect();
        for constant in declared {
            let name = values.name(constant);
            let expected = values
                .evaluate_on(constant, Engine::Executor)
                .expect("the executor answers");
            if PATCHER {
                let ran = values.evaluate_on(constant, Engine::Native);
                assert_eq!(Ok(&expected), ran.as_ref(), "{name:?} on native code");
            }
            assert_eq!(
                expected,
                values.evaluate(constant),
                "{name:?} under the policy"
            );
        }
    }

    #[test]
    fn a_run_reaching_a_goal_blames_it()
    {
        let mut goals = program(
            r#"def later : Integer ;
def copy : Integer ; def copy = later ;
def suspended : +U (-F Integer) ;
def forced : +U (-F Integer) ; def forced = thunk { become force suspended } ;
def function : +U (Integer -> -F Integer) ;
def applied : +U (-F Integer) ; def applied = thunk { become (force function)(1) } ;
def untouched : +U (-F Integer) ; def untouched = thunk { return 3 } ;
def holder : +U (-F Integer) ; def holder = thunk { become force suspended } ;
def kept : +U (-F (+U (-F Integer))) ; def kept = thunk { return holder } ;"#,
        );
        for (name, goal) in [
            ("later", "later"),
            ("copy", "later"),
            ("forced", "suspended"),
            ("applied", "function"),
        ] {
            assert_eq!(
                run(&mut goals, SurfaceName::from(name)),
                Evaluation::Blamed(SurfaceName::from(goal)),
                "`{name}` is blamed on the goal it reaches"
            );
        }
        assert_eq!(
            run(&mut goals, SurfaceName::from("untouched")).to_string(),
            "3",
            "a run that reaches no goal is not blamed for one beside it"
        );
        assert_eq!(
            run(&mut goals, SurfaceName::from("kept")).to_string(),
            "thunk { force suspended }",
            "a goal under a suspension the run returns is not reached"
        );
        let rendered = run(&mut goals, SurfaceName::from("forced")).to_string();
        assert_eq!(rendered.split('`').nth(1), Some("suspended"));
    }

    #[test]
    fn a_reference_the_machine_cannot_carry_is_never_run()
    {
        let mut carried = program(
            r#"def bad : Integer ; def bad = "text" ;
def uses : Integer ; def uses = bad ;
def later : Integer ; def lost = missing ; def answer = 42 ;"#,
        );
        let before = carried.arena.watermark();
        for name in ["bad", "uses"] {
            assert_eq!(
                run(&mut carried, SurfaceName::from(name)),
                Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("bad"))),
                "`{name}` reaches the refused declaration and never runs"
            );
        }
        assert_eq!(
            carried.evaluate(ConstantIndex::from(9_usize)),
            Evaluation::Unrunnable(Unrunnable::Undeclared(ConstantIndex::from(9_usize))),
            "a position past the program holds nothing to run"
        );
        assert_eq!(
            carried.arena.watermark(),
            before,
            "blocked runs mint no commands"
        );
        assert_eq!(
            run(&mut carried, SurfaceName::from("lost")),
            Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("lost")))
        );
        assert_eq!(
            run(&mut carried, SurfaceName::from("answer")).to_string(),
            "42"
        );
    }

    #[test]
    fn a_refused_declaration_runs_only_as_its_own_root()
    {
        let mut refused = program(
            r#"def wrong : String ; def wrong = 42 ;
def bad : Integer ; def bad = "text" ;
def leans : String ; def leans = bad ;
def lost = missing ; def answer = 42 ;"#,
        );
        let at = |program: &Program<'_>, name: &str| {
            program
                .declarations
                .iter()
                .find(|&(_, declared)| declared.name == SurfaceName::from(name))
                .map(|(&constant, _)| constant)
                .expect("the program declares the name")
        };
        let wrong = at(&refused, "wrong");
        assert_eq!(
            refused.evaluate_refused(wrong).to_string(),
            "42",
            "the refused body runs as its own root"
        );
        assert_eq!(
            refused.evaluate(wrong),
            Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("wrong"))),
            "the strict run still refuses it"
        );
        let leans = at(&refused, "leans");
        assert_eq!(
            refused.evaluate_refused(leans),
            Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("bad"))),
            "another refused declaration it reaches stops the run"
        );
        let lost = at(&refused, "lost");
        assert_eq!(
            refused.evaluate_refused(lost),
            Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("lost"))),
            "a body the lowering refused has nothing to run"
        );
        let answer = at(&refused, "answer");
        assert_eq!(
            refused.evaluate_refused(answer).to_string(),
            "42",
            "an accepted declaration runs alike either way"
        );
    }

    /// A code focuses and runs to the type it quotes, through any chain of
    /// references to it, as the run of an interface operation at a type
    /// argument needs (#452); only a body that did not focus is listed as a
    /// refusal.
    #[test]
    fn a_code_and_every_reference_to_it_run_to_the_type_it_quotes()
    {
        let mut codes = program(
            r"def small : Type ; def small = Integer ;
def alias : Type ; def alias = small ;
def again : Type ; def again = alias ;
def wide : Type ; def wide = String ;
def law(p : Path(Integer, 1, 1)) -> -F Path(Integer, 1, 1) {
  transport(\y. Path(Integer, y, y), p then p, here(1))
}",
        );
        assert!(
            codes
                .focus_refusals()
                .map(|(name, _)| name)
                .eq([SurfaceName::from("law")]),
            "every code focuses; the transport the machine does not lower is the one refusal"
        );
        for (name, spelled) in [
            ("small", "pure Integer"),
            ("alias", "pure Integer"),
            ("again", "pure Integer"),
            ("wide", "pure String"),
        ] {
            assert_eq!(
                run(&mut codes, SurfaceName::from(name)).to_string(),
                spelled,
                "`{name}` runs to the type it quotes"
            );
        }
    }

    /// A declaration whose body did not focus blocks its own run and every
    /// run that reaches it, and no run that only carries it.
    #[test]
    fn a_body_that_did_not_focus_is_carried_until_reached()
    {
        let mut laws = program(
            r"def law(p : Path(Integer, 1, 1)) -> -F Path(Integer, 1, 1) {
  transport(\y. Path(Integer, y, y), p then p, here(1))
}
def reached : +U (-F Path(Integer, 1, 1)) ; def reached = thunk { law(here(1)) } ;
def kept : +U (-F (+U (-F Path(Integer, 1, 1)))) ; def kept = thunk { return reached } ;",
        );
        for name in ["law", "reached"] {
            let evaluation = run(&mut laws, SurfaceName::from(name));
            assert!(
                matches!(
                    evaluation,
                    Evaluation::Unrunnable(Unrunnable::Unfocused {
                        declaration,
                        refusal: FocusRefusal::ElementTransport(_, gandr_core_sequent::MotiveHead::Path),
                    }) if declaration == SurfaceName::from("law")
                ),
                "`{name}` reaches the unfocused body: {evaluation}"
            );
        }
        assert_eq!(
            run(&mut laws, SurfaceName::from("kept")).to_string(),
            "thunk { law((thunk { fn (a) { a } }, thunk { fn (a) { a } })) }",
            "a run that carries the unfocused body without reaching it returns"
        );
    }

    /// A static code has no image in the machine, so a run that reaches one
    /// through a reference is blocked by it even where the run would only
    /// carry it, as it carries a body that did not focus for another reason.
    #[test]
    fn a_run_reaching_a_static_code_is_blocked_by_it()
    {
        let mut codes = program(
            r"def twice : Type -> Type ; def twice = \Y. Y * Y ;
def again : Type -> Type ; def again = twice ;
def held : +U (-F (Type -> Type)) ; def held = thunk { return twice } ;
def kept : +U (-F (+U (-F (Type -> Type)))) ; def kept = thunk { return held } ;",
        );
        for name in ["twice", "again", "held", "kept"] {
            let evaluation = run(&mut codes, SurfaceName::from(name));
            assert!(
                matches!(
                    evaluation,
                    Evaluation::Unrunnable(Unrunnable::Unfocused {
                        declaration,
                        refusal: FocusRefusal::Code(_),
                    }) if declaration == SurfaceName::from("twice")
                ),
                "`{name}` reaches the static code: {evaluation}"
            );
        }
    }

    /// Only a member of a module a signature coerced is hidden: beside such a
    /// module, a run naming a declaration outside it is spelled, not sealed.
    #[test]
    fn a_run_naming_a_declaration_outside_every_sealed_module_is_spelled()
    {
        let mut beside = program(
            r"theory Pointed {
  sort T : Type;
  oper z : T;
}
module ZeroPointed : Model(Pointed) {
  type T = Integer;
  def z = 0;
}
def helper(x : Integer) -> -F Integer { x }
def wrap : Integer => Integer ; def wrap = fn (n) { become helper(n) } ;",
        );
        let evaluation = run(&mut beside, SurfaceName::from("wrap"));
        assert!(
            matches!(evaluation, Evaluation::Value(_)),
            "`wrap` names `helper`, which no signature hides: {evaluation}"
        );
    }

    /// A run whose value names a member its module's signature hides is
    /// opaque at that module, reported with the declared type of the
    /// declaration run, as the program spelled it when it was built.
    #[test]
    fn a_run_naming_a_hidden_member_is_opaque_at_its_module()
    {
        let mut hiding = program(
            r"theory Pointed {
  sort T : Type;
  oper z : T;
}
module Stepped : Model(Pointed) {
  type T = Integer => Integer;
  def step(x : Integer) -> -F Integer { x }
  def z : T ; def z = fn (n) { become step(n) } ;
}",
        );
        assert_eq!(
            run(&mut hiding, SurfaceName::from("z")),
            Evaluation::Sealed(SealedRun {
                module: String::from("Stepped"),
                declared: String::from("Integer => Integer"),
            }),
            "`z` runs to a function applying `step`, which the signature hides"
        );
    }

    #[test]
    fn each_outcome_class_has_its_status()
    {
        let mut written = program(
            r#"def later : Integer ; def answer = 42 ; def copy : Integer ; def copy = later ;
def bad : Integer ; def bad = "text" ;"#,
        );
        let rows = [
            (
                run(&mut written, SurfaceName::from("answer")),
                RunStatus::Value,
            ),
            (
                run(&mut written, SurfaceName::from("copy")),
                RunStatus::Failed,
            ),
            (
                run(&mut written, SurfaceName::from("bad")),
                RunStatus::Unreached,
            ),
            (
                Evaluation::Stuck(Stuck::UndefinedConstant(ConstantIndex::from(0_usize))),
                RunStatus::Failed,
            ),
            (
                Evaluation::Unfinished(Unfinished::Declined(Declined::Exhausted(
                    Status::FuelExhausted,
                ))),
                RunStatus::Failed,
            ),
        ];
        for (evaluation, status) in rows {
            assert_eq!(
                evaluation.status(),
                status,
                "{evaluation} has its pinned status"
            );
        }
    }

    #[test]
    fn the_run_target_is_the_last_name_declared()
    {
        let several = program(r#"def a = 1 ; def b = 2 ; def c = 3 ;"#);
        assert_eq!(
            several.target(),
            Maybe::Present(ConstantIndex::from(2_usize)),
            "the last of several names"
        );
        let redeclared = program(r#"def x : Integer ; def y = 1 ; def x = 2 ;"#);
        assert_eq!(
            redeclared.target(),
            Maybe::Present(ConstantIndex::from(1_usize)),
            "a later declaration of an earlier name keeps that name's position"
        );
        for (position, name) in [(0_usize, "x"), (1_usize, "y")] {
            assert_eq!(
                redeclared.name(ConstantIndex::from(position)),
                Maybe::Present(SurfaceName::from(name))
            );
        }
        assert_eq!(
            redeclared.name(ConstantIndex::from(usize::MAX)),
            Maybe::Absent(super::declaration_name::Absent::Undeclared)
        );
        let none = program(r#"// nothing declared"#);
        assert_eq!(
            none.target(),
            Maybe::Absent(run_target::Absent::NoDeclaration),
            "a source of no name has no target"
        );
        assert_eq!(
            none.name(ConstantIndex::from(0_usize)),
            Maybe::Absent(super::declaration_name::Absent::Undeclared)
        );
        assert!(
            program("").declarations.is_empty(),
            "empty input admits no declaration"
        );
    }

    /// #1105: a source's final expression is its run target, admitted after
    /// every name it declares, and what the source runs: a value written
    /// there is returned, a call is run.
    #[test]
    fn a_final_expression_is_the_run_target_1105()
    {
        let mut redeclared = program(
            r#"def x : Integer ; def y = 1 ; def x = 2 ;
x"#,
        );
        let after = ConstantIndex::from(2_usize);
        assert_eq!(
            redeclared.target(),
            Maybe::Present(after),
            "the target follows every name, a later declaration of an earlier one included"
        );
        assert_eq!(
            redeclared.evaluate(after).to_string(),
            "2",
            "a value target is returned"
        );
        let mut called = program(
            r#"def answer = 42 ;
def same(a : Type, x : a) -> -F a { return x }
same(Integer, answer)"#,
        );
        assert_eq!(called.target(), Maybe::Present(after));
        let evaluation = called.evaluate(after);
        assert!(
            matches!(evaluation, Evaluation::Value(_)),
            "a call target runs to a value: {evaluation}"
        );
        assert_eq!(evaluation.to_string(), "42", "the call's value");
    }

    #[test]
    fn terminal_classification_preserves_declaration_identity()
    {
        let written = program(
            r#"def answer = 42 ; def later : Integer ;
def bad : Integer ; def bad = "text" ;
def law(p : Path(Integer, 1, 1)) -> -F Path(Integer, 1, 1) {
  transport(\y. Path(Integer, y, y), p then p, here(1))
}"#,
        );
        let defined = written.met(ConstantIndex::from(0_usize));
        assert_eq!(
            defined,
            Evaluation::Unfinished(Unfinished::Inconsistent(ConstantIndex::from(0_usize)))
        );
        assert_eq!(
            written.met(ConstantIndex::from(1_usize)),
            Evaluation::Blamed(SurfaceName::from("later"))
        );
        assert_eq!(
            written.met(ConstantIndex::from(2_usize)),
            Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("bad")))
        );
        assert!(
            matches!(written.met(ConstantIndex::from(3_usize)), Evaluation::Unrunnable(
            Unrunnable::Unfocused { declaration, .. }) if declaration == SurfaceName::from("law"))
        );
        let absent = written.met(ConstantIndex::from(99_usize));
        assert_eq!(
            absent,
            Evaluation::Unrunnable(Unrunnable::Undeclared(ConstantIndex::from(99_usize)))
        );
        for (evaluation, expected) in [(defined, 0_usize), (absent, 99_usize)] {
            assert!(
                evaluation
                    .to_string()
                    .split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq([expected])
            );
        }
    }

    #[test]
    fn a_constructed_terminal_blames_its_first_opaque_field()
    {
        let goals = program("def first : Integer ; def second : Integer ;");
        let mut core = gandr_core_term::CoreArena::new();
        let unit = core.value_unit();
        let first = core.value_constant(ConstantIndex::from(0_usize));
        let second = core.value_constant(ConstantIndex::from(1_usize));
        let nested = core.value_tuple(&[second, first]);
        let outer = core.value_tuple(&[unit, nested]);
        let returned = core.computation_return(outer);
        let mut commands = gandr_core_sequent::CommandArena::default();
        let mut provenance = gandr_core_sequent::Provenance::new();
        let command =
            gandr_core_sequent::focus_computation(&core, returned, &mut commands, &mut provenance)
                .expect("the constructed terminal focuses");
        let mut store = Store::new();
        let outcome = gandr_runtime_emitter::evaluate_on(
            Tier::Executor,
            &commands,
            &goals.definitions,
            command,
            Fuel::from(100_usize),
            &mut store,
        )
        .expect("the constructed terminal runs");
        assert_eq!(
            goals.halted(&store, outcome),
            Err(Evaluation::Blamed(SurfaceName::from("second")))
        );
    }

    #[test]
    fn structured_values_keep_repeated_references_and_field_order()
    {
        let names = program("def first : Integer ; def second : Integer ;");
        let mut core = gandr_core_term::CoreArena::new();
        let first = core.value_constant(ConstantIndex::from(0_usize));
        let second = core.value_constant(ConstantIndex::from(1_usize));
        let nested = core.value_tuple(&[second, first]);
        let outer = core.value_tuple(&[first, nested]);
        let mut referred = super::references(&core, outer);
        referred.sort_unstable();
        assert_eq!(referred.as_slice(), &[
            ConstantIndex::from(0_usize),
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize)
        ]);
        let returned = core.computation_return(outer);
        let spelled = |core: &gandr_core_term::CoreArena, returned| {
            names
                .spell(core, returned)
                .map(|spelling| spelling.as_ref().to_owned())
        };
        assert_eq!(
            spelled(&core, returned),
            Ok(String::from("(first, (second, first))"))
        );
        for (summand, expected) in [
            (0_usize, "+{.0 = second}"),
            (1, "+{.1 = second}"),
            (2, "+{.2 = second}"),
        ] {
            let injected = core.value_injection(summand.into(), second);
            let returned = core.computation_return(injected);
            assert_eq!(spelled(&core, returned), Ok(String::from(expected)));
        }
    }

    #[test]
    fn a_skipped_admission_position_holds_no_declaration()
    {
        let mut program = program(
            "module M { type T = Integer ; def seed : T ; def seed = 41 ; }\ndef copy : Integer \
             ;\ndef copy = M.seed ;",
        );
        assert_eq!(
            program
                .declarations
                .keys()
                .map(|&constant| usize::from(constant))
                .collect::<Vec<_>>(),
            [1_usize, 2_usize],
            "the type member takes the first position and declares nothing there"
        );
        assert_eq!(
            program.name(ConstantIndex::from(0_usize)),
            Maybe::Absent(super::declaration_name::Absent::Undeclared)
        );
        assert_eq!(
            program.evaluate(ConstantIndex::from(0_usize)),
            Evaluation::Unrunnable(Unrunnable::Undeclared(ConstantIndex::from(0_usize))),
            "the skipped position holds nothing to run"
        );
        assert_eq!(
            program.target(),
            Maybe::Present(ConstantIndex::from(2_usize))
        );
        assert!(
            matches!(run(&mut program, SurfaceName::from("copy")), Evaluation::Value(ref value) if value.as_ref() == "41"),
            "a reference past the skipped position reads the declaration it names"
        );
    }

    /// The thunk declared as `name` in [`LOOPS`] is a thunk whose force, on
    /// `tier`, runs until its 2²⁵ jumps are spent or its heap fills, without
    /// filling the frame region. Each pass gives its window back, so a pass
    /// holding a frame would fill the frames within those jumps;
    /// `gandr-core-sequent`'s loop suite holds the plain loop to that
    /// contrast. A tier this host lacks holds nothing to run.
    ///
    /// # Specification
    /// trivial.
    fn holds_no_frame(
        name: SurfaceName<'_>,
        tier: Tier,
    )
    {
        if matches!(tier, Tier::Native) && !PATCHER {
            return;
        }
        let mut program = program(LOOPS);
        let position = program
            .declarations
            .iter()
            .find(|&(_, declared)| declared.name == name)
            .map(|(&constant, _)| constant)
            .expect("the program declares the name");
        let (returned, forced) = program
            .entries(position, Reach::Value)
            .expect("the declaration focuses");
        let run = |root, fuel| {
            gandr_runtime_emitter::evaluate_on(
                tier,
                &program.arena,
                &program.definitions,
                root,
                Fuel::from(fuel),
                &mut Store::new(),
            )
        };
        assert!(
            matches!(
                run(returned, super::RUN_BUDGET),
                Ok(super::Outcome::Halted(_))
            ),
            "`{name}` is a thunk on {tier:?}"
        );
        let spent = run(forced, 1_usize << 25_u32);
        assert!(
            matches!(
                spent,
                Err(Declined::Exhausted(
                    Status::FuelExhausted | Status::HeapExhausted
                ))
            ),
            "`{name}` holds no frame on {tier:?}: {spent:?}"
        );
    }

    /// Four loops a pass of runs through: a statement, a bound statement, a
    /// bound inner loop that breaks, and a `while` whose test always holds.
    const LOOPS: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
         def tick(n : Nat) -> -F Unit { return unit }\n\
         def spin : +U (-F Nat) ;\ndef spin = thunk { loop { tick(Zero); } } ;\n\
         def bound : +U (-F Nat) ;\ndef bound = thunk { loop { run u <- tick(Zero) ; continue } } ;\n\
         def broken : +U (-F Nat) ;\ndef broken = thunk { loop { run u <- loop { break } ; continue } } ;\n\
         def tested : +U (-F Nat) ;\ndef tested = thunk { while 1 > 0 { tick(Zero) } ; return Zero } ;\n";

    // One test per loop and tier: each spends its whole fuel, so the eight
    // runs together passed the thirty-second bound on a loaded machine
    // (#1857).

    #[test]
    fn a_loop_runs_in_constant_continuation()
    {
        holds_no_frame(SurfaceName::from("spin"), Tier::Executor);
    }

    #[test]
    fn a_loop_runs_in_constant_continuation_natively()
    {
        holds_no_frame(SurfaceName::from("spin"), Tier::Native);
    }

    #[test]
    fn a_bound_loop_body_runs_in_constant_continuation()
    {
        holds_no_frame(SurfaceName::from("bound"), Tier::Executor);
    }

    #[test]
    fn a_bound_loop_body_runs_in_constant_continuation_natively()
    {
        holds_no_frame(SurfaceName::from("bound"), Tier::Native);
    }

    #[test]
    fn a_loop_bound_to_an_inner_break_runs_in_constant_continuation()
    {
        holds_no_frame(SurfaceName::from("broken"), Tier::Executor);
    }

    #[test]
    fn a_loop_bound_to_an_inner_break_runs_in_constant_continuation_natively()
    {
        holds_no_frame(SurfaceName::from("broken"), Tier::Native);
    }

    #[test]
    fn a_while_loop_runs_in_constant_continuation()
    {
        holds_no_frame(SurfaceName::from("tested"), Tier::Executor);
    }

    #[test]
    fn a_while_loop_runs_in_constant_continuation_natively()
    {
        holds_no_frame(SurfaceName::from("tested"), Tier::Native);
    }

    /// The source of a function whose exits stand one and two matches deep
    /// under a bound statement, and of its runs over three inputs.
    const PICK: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
         def pick(n : Nat) -> -F Nat {\n  run m <- case n {\n    Zero => return n,\n    \
         Succ(p) => {\n      run q <- case p { Zero => return n, Succ(r) => pure r } ;\n      \
         pure q\n    },\n  } ;\n  return Succ(m)\n}\n\
         def bound(n : Nat) -> -F Nat {\n  run m <- case n -> -F Nat { Zero => pure n, Succ(p) => pure p } ;\n  \
         return Succ(m)\n}\n\
         def zero : +U (-F Nat) ;\ndef zero = thunk { become pick(Zero) } ;\n\
         def one : +U (-F Nat) ;\ndef one = thunk { become pick(Succ(Zero)) } ;\n\
         def three : +U (-F Nat) ;\ndef three = thunk { become pick(Succ(Succ(Succ(Zero)))) } ;\n";

    #[test]
    fn a_nested_return_delivers_its_value_from_its_function()
    {
        let mut program = program(PICK);
        for (name, delivered) in [
            ("zero", "Zero"),
            ("one", "Succ(Zero)"),
            ("three", "Succ(Succ(Zero))"),
        ] {
            let evaluation = run(&mut program, SurfaceName::from(name));
            assert_eq!(
                evaluation.to_string(),
                delivered,
                "`{name}` delivers what its exit returns: {evaluation:?}"
            );
        }
    }

    /// What the IL reachable from the definition of `name` holds: its
    /// commands and its consumers.
    ///
    /// # Specification
    /// trivial.
    fn reached(
        program: &Program<'_>,
        name: SurfaceName<'_>,
    ) -> (
        Vec<gandr_core_sequent::CommandNode>,
        Vec<gandr_core_sequent::ConsumerNode>,
    )
    {
        use gandr_core_sequent::CommandNode;
        use gandr_core_sequent::ConsumerNode;
        use gandr_core_sequent::ProducerNode;

        /// One node of the walk.
        enum Node
        {
            /// A producer.
            Producer(gandr_core_sequent::ProducerId),
            /// A consumer.
            Consumer(gandr_core_sequent::ConsumerId),
            /// A command.
            Command(gandr_core_sequent::CommandId),
        }
        let position = program
            .declarations
            .iter()
            .find(|&(_, declared)| declared.name == name)
            .map(|(&constant, _)| constant)
            .expect("the program declares the name");
        let Some(gandr_core_sequent::Definition::Transparent(root)) =
            program.definitions.get(position)
        else {
            panic!("`{name}` focuses to a value");
        };
        let (mut commands, mut consumers) = (Vec::new(), Vec::new());
        let mut pending = vec![Node::Producer(root)];
        while let Some(next) = pending.pop() {
            match next {
                Node::Producer(id) => match program.arena.producer(id) {
                    Some(
                        &(ProducerNode::Thunk { body }
                        | ProducerNode::Fixpoint { body, .. }
                        | ProducerNode::Mu { body }),
                    ) => pending.push(Node::Command(body)),
                    Some(&ProducerNode::Cocase { ref arms }) => {
                        pending.extend(arms.iter().map(|arm| Node::Command(arm.body)));
                    },
                    Some(&ProducerNode::Constructor {
                        ref producers,
                        consumers: ref fields,
                        ..
                    }) => {
                        pending.extend(producers.iter().copied().map(Node::Producer));
                        pending.extend(fields.iter().copied().map(Node::Consumer));
                    },
                    _ => {},
                },
                Node::Consumer(id) => {
                    let Some(node) = program.arena.consumer(id)
                    else {
                        continue;
                    };
                    match *node {
                        ConsumerNode::MuTilde { body } => pending.push(Node::Command(body)),
                        ConsumerNode::Destructor {
                            ref producers,
                            consumers: ref fields,
                            ..
                        } => {
                            pending.extend(producers.iter().copied().map(Node::Producer));
                            pending.extend(fields.iter().copied().map(Node::Consumer));
                        },
                        ConsumerNode::Case { ref arms } => {
                            pending.extend(arms.iter().map(|arm| Node::Command(arm.body)));
                        },
                        ConsumerNode::DataCase {
                            ref branches, then, ..
                        } => {
                            pending.extend(branches.iter().copied().map(Node::Producer));
                            pending.push(Node::Consumer(then));
                        },
                        ConsumerNode::Covariable(_)
                        | ConsumerNode::Select { .. }
                        | ConsumerNode::ListFold { .. }
                        | ConsumerNode::Top => {},
                    }
                    consumers.push(node.clone());
                },
                Node::Command(id) => {
                    let Some(node) = program.arena.command(id)
                    else {
                        continue;
                    };
                    if let CommandNode::Cut {
                        producer, consumer, ..
                    } = *node
                    {
                        pending.extend([Node::Producer(producer), Node::Consumer(consumer)]);
                    }
                    commands.push(node.clone());
                },
            }
        }

        (commands, consumers)
    }

    #[test]
    fn an_exit_under_nesting_cuts_its_value_against_the_return_continuation()
    {
        use gandr_core_sequent::CommandNode;
        use gandr_core_sequent::ConsumerNode;
        use gandr_core_sequent::ProducerNode;

        let program = program(PICK);
        let (commands, consumers) = reached(&program, SurfaceName::from("pick"));
        assert!(
            commands
                .iter()
                .all(|command| matches!(*command, CommandNode::Cut { .. })),
            "an exit installs no delimiter, no handler and no resumption: {commands:?}"
        );
        assert!(
            !consumers
                .iter()
                .any(|consumer| matches!(*consumer, ConsumerNode::MuTilde { .. })),
            "no frame stands between an exit and the function's return continuation: \
             {consumers:?}"
        );
        let exits = commands
            .iter()
            .filter(|command| {
                matches!(
                    **command,
                    CommandNode::Cut { producer, consumer, .. }
                        if matches!(program.arena.producer(producer), Some(&(ProducerNode::Variable { .. } | ProducerNode::Constructor { .. })))
                            && matches!(program.arena.consumer(consumer), Some(&ConsumerNode::Covariable(_)))
                )
            })
            .count();
        assert_eq!(
            exits, 3_usize,
            "each of the three exits is the cut of its value against a covariable"
        );
        let (_, bound) = reached(&program, SurfaceName::from("bound"));
        assert!(
            bound
                .iter()
                .any(|consumer| matches!(*consumer, ConsumerNode::MuTilde { .. })),
            "a match bound by a statement with no exit continues through a frame: {bound:?}"
        );
    }
}
