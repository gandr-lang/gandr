//! The run stage: a checked module focused into the command IL, one
//! declaration run on the L machine, and its terminal read back and spelled.
//!
//! # A program is its declarations
//!
//! The fragment has no top-level expression, so a program is the module's
//! declarations, each a constant the machine unfolds on demand. An accepted
//! declaration's elaborated body is focused once, when the program is built; a
//! declaration owed its body, refused, or whose body does not focus is carried
//! as itself, the machine's opaque constant. `gandr run` runs the last name
//! the source declares; the session and the corpus run any accepted
//! declaration by its admission position.
//!
//! # Running a declaration
//!
//! A declaration is a value. Running it returns that value, and when the value
//! is a thunk — a computation suspended, a function's body among them — the
//! thunk is forced, so `def main = thunk { ret 42 }` runs to `42` and a
//! function runs to its own terminal, `<fun>`. The run's terminal is read back
//! into the core and spelled; the spelling is the one `gandr run` prints, the
//! session's value line carries and a `runs` expectation compares.
//!
//! # Classification
//!
//! A run that returns a value succeeds. A run that reaches a declaration owed
//! its body — returning it, forcing it, applying it or matching on it — is
//! blamed on that declaration, the obligation it met; any other stop short of
//! a value is stuck; a run the machine could not finish, its step budget spent
//! or its store refusing, is unfinished. Each of these reached the machine. A
//! declaration that refers, directly or through others, to one that was
//! refused or did not focus never reaches it: the reference is found by
//! walking the program's references before any command runs.

use core::fmt;

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
use gandr_core_sequent::Machine;
use gandr_core_sequent::MachineFault;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::StepCount;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_value;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_surface_corpus::RunSpelling;
use gandr_surface_corpus::Runner;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SurfaceName;
use quenchant_shape::shape::Maybe;

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

/// The transitions one run may spend: far past any run the fragment can
/// write, which has no recursion and so always halts, and the bound that
/// keeps a run of a later fragment from looping unobserved.
const RUN_BUDGET: usize = 1_usize << 24_u32;

/// A checked module, focused and ready to run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program<'source>
{
    /// Every focused definition, and each command minted to run one.
    arena: CommandArena,
    /// What each constant unfolds to, by admission position.
    definitions: Definitions,
    /// Each declaration's name and standing, by admission position.
    declarations: Vec<Declared<'source>>,
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
    /// The machine carries it as itself, for the reason given.
    Opaque(Opacity),
}

/// Why the machine carries a declaration as itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opacity
{
    /// It is owed its body: running into it is blame.
    Owed,
    /// It was refused, by the lowering or the checker, or the checker accepted
    /// it and recorded no body: there is nothing to run.
    Refused,
    /// Its body did not focus.
    Unfocused(FocusRefusal),
}

/// A value, spelled: the text `gandr run` prints for a run that returned one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueSpelling(String);

impl AsRef<str> for ValueSpelling
{
    /// The spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
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
        f.write_str(&self.0)
    }
}

/// What running one declaration came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evaluation<'source>
{
    /// The run returned a value, or a function: its spelling.
    Value(ValueSpelling),
    /// The run reached the named declaration, owed its body.
    Blamed(SurfaceName<'source>),
    /// The run stopped short of a value.
    Stuck(Stuck),
    /// The machine could not finish the run.
    Unfinished(Unfinished),
    /// The declaration never reached the machine.
    Unrunnable(Unrunnable<'source>),
}

/// Why the machine could not finish a run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unfinished
{
    /// The machine faulted: its step budget ran out or its store refused.
    Fault(MachineFault),
    /// The run's terminal has no reading in the core.
    Readback(ReadbackRefusal),
    /// The machine carried as itself a constant the program defines, which
    /// the program's own definitions rule out.
    Inconsistent(ConstantIndex),
}

/// Why a declaration never reached the machine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unrunnable<'source>
{
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
    /// - ensures: a value is [`RunStatus::Value`]; a blamed, stuck or
    ///   unfinished run [`RunStatus::Failed`]; an unrunnable declaration
    ///   [`RunStatus::Unreached`].
    /// - provides: the one classification the driver's exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run of each class the fragment can write, each
    ///   asserted at its exact status.
    /// - witness: `evaluate::tests::each_outcome_class_has_its_status`
    #[anodized::spec(ensures: |ret| match *self {
        Self::Value(_) => matches!(ret, RunStatus::Value),
        Self::Blamed(_) | Self::Stuck(_) | Self::Unfinished(_) => matches!(ret, RunStatus::Failed),
        Self::Unrunnable(_) => matches!(ret, RunStatus::Unreached),
    })]
    #[inline]
    #[must_use]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            | Self::Value(_) => RunStatus::Value,
            | Self::Blamed(_) | Self::Stuck(_) | Self::Unfinished(_) => RunStatus::Failed,
            | Self::Unrunnable(_) => RunStatus::Unreached,
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
    /// - ensures: values retain their spelling; other outcomes identify their
    ///   class and the declaration, position or machine reason they carry.
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
            | Self::Value(ref value) => fmt::Display::fmt(value, f),
            | Self::Blamed(goal) => write!(f, "blame: `{goal}` is owed its body"),
            | Self::Stuck(ref stuck) => write!(f, "stuck: {stuck}"),
            | Self::Unfinished(Unfinished::Fault(fault)) => write!(f, "unfinished: {fault}"),
            | Self::Unfinished(Unfinished::Readback(refusal)) => {
                write!(f, "unfinished: {refusal}")
            },
            | Self::Unfinished(Unfinished::Inconsistent(constant)) => write!(
                f,
                "unfinished: the machine carried defined constant {} as itself",
                usize::from(constant)
            ),
            | Self::Unrunnable(Unrunnable::Undeclared(constant)) => write!(
                f,
                "unrunnable: no declaration sits at admission position {}",
                usize::from(constant)
            ),
            | Self::Unrunnable(Unrunnable::Refused(declaration)) => {
                write!(f, "unrunnable: `{declaration}` was refused")
            },
            | Self::Unrunnable(Unrunnable::Unfocused {
                declaration,
                refusal: FocusRefusal::Code(_),
            }) => write!(
                f,
                "unrunnable: `{declaration}` is a code, which the machine carries no image of"
            ),
            | Self::Unrunnable(Unrunnable::Unfocused {
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
    ///   over `core`; their admission indices may be sparse.
    /// - ensures: one entry per declaration of `module`, packed in module
    ///   order. A declaration checked or synthesised has its elaborated body
    ///   focused and is defined as it; one owed its body is carried as itself;
    ///   one refused by the lowering or the checker, or whose body does not
    ///   focus, is carried as itself and never run. Input admission indices
    ///   select verdicts; program positions index the packed entries.
    /// - provides: the program every run of the module's declarations shares.
    /// - fails: never; a body that does not focus is the declaration's
    ///   standing, not a failure of the program.
    /// - panics: none.
    /// - intension: one focusing per accepted declaration; nothing runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sources holding an accepted, an owed, a refused and
    ///   an unfocusable declaration are built and each run asserted at its
    ///   exact outcome. A sparse literal declaration retains its name and value
    ///   at its packed program position. Sparse cross-declaration references
    ///   are outside these fixtures.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::sparse_admission_positions_keep_program_order`
    #[anodized::spec(
        ensures: |ref ret| ret.declarations.len() == module.declarations().len()
            && usize::from(ret.definitions.len()) == ret.declarations.len()
            && ret.declarations.iter().zip(module.declarations()).enumerate()
                .all(|(position, (declared, lowered))| declared.name == lowered.name()
                    && match (ret.definitions.get(ConstantIndex::from(position)), &declared.slot) {
                        (Some(Definition::Transparent(producer)), &Slot::Defined(_)) => ret.arena.producer(producer).is_some(),
                        (Some(Definition::Opaque), &Slot::Opaque(_)) => true,
                        _ => false,
                    })
    )]
    #[must_use]
    pub(crate) fn new(
        core: &CoreArena,
        module: &LoweredModule<'source>,
        verdicts: &ModuleReport,
    ) -> Self
    {
        let mut arena = CommandArena::default();
        let mut provenance = Provenance::new();
        let mut definitions = Definitions::new();
        let mut declarations = Vec::with_capacity(module.declarations().len());
        let mut judged = verdicts.judged().iter().peekable();
        for lowered in module.declarations() {
            let constant = lowered.constant();
            let verdict = judged
                .next_if(|answer| answer.constant() == constant)
                .map(Judged::verdict);
            let body = verdicts.definitions().get(&constant).copied();
            let (definition, slot) = match (verdict, body) {
                | (Some(Verdict::Checked { .. } | Verdict::Synthesised { .. }), Some(body)) => {
                    match focus_value(core, body, &mut arena, &mut provenance) {
                        | Ok(producer) => (
                            Definition::Transparent(producer),
                            Slot::Defined(references(core, body)),
                        ),
                        | Err(refusal) => (
                            Definition::Opaque,
                            Slot::Opaque(Opacity::Unfocused(refusal)),
                        ),
                    }
                },
                | (Some(Verdict::Owed(_)), _) => (Definition::Opaque, Slot::Opaque(Opacity::Owed)),
                | (
                    Some(
                        Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Refused(_),
                    )
                    | None,
                    _,
                ) => (Definition::Opaque, Slot::Opaque(Opacity::Refused)),
            };
            let _position = definitions.push(definition);
            declarations.push(Declared {
                name: lowered.name(),
                slot,
            });
        }
        Self {
            arena,
            definitions,
            declarations,
        }
    }

    /// The declaration `gandr run` runs: the last name the source declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the highest admission position of the program, which is the
    ///   name the source declared last for the first time.
    /// - provides: the run target of a source with no top-level expression.
    /// - fails: [`run_target::Absent::NoDeclaration`] when the source declares
    ///   no name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of several names, a later declaration of an
    ///   earlier name among them, and a source of none.
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    #[anodized::spec(ensures: |ret| match ret {
        Maybe::Present(last) => usize::from(last).checked_add(1_usize) == Some(self.declarations.len()),
        Maybe::Absent(run_target::Absent::NoDeclaration) => self.declarations.is_empty(),
    })]
    #[inline]
    pub fn target(&self) -> Maybe<ConstantIndex, run_target::Absent>
    {
        match self.declarations.len().checked_sub(1_usize) {
            | Some(last) => Maybe::Present(ConstantIndex::from(last)),
            | None => Maybe::Absent(run_target::Absent::NoDeclaration),
        }
    }

    /// The name of the declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing; any admission position may be queried.
    /// - ensures: the name stored at the exact position, or `Undeclared` when
    ///   the position is outside the declarations, without truncating the
    ///   index.
    /// - fails: an absent name is the typed absence, never a substitute name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct names retain their positions across a later
    ///   definition of an earlier name; empty and maximal-index queries are
    ///   absent.
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    #[anodized::spec(ensures: |ret| match (self.declarations.get(usize::from(constant)), ret) {
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
        match self.declarations.get(usize::from(constant)) {
            | Some(declared) => Maybe::Present(declared.name),
            | None => Maybe::Absent(declaration_name::Absent::Undeclared),
        }
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
    /// - hypothesis: L3 — two code refusals retain order across defined, owed
    ///   and refused declarations; other focusing refusal kinds are not
    ///   generated.
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    #[inline]
    pub fn focus_refusals(&self)
    -> impl Iterator<Item = (SurfaceName<'source>, FocusRefusal)> + '_
    {
        self.declarations
            .iter()
            .filter_map(|declared| match declared.slot {
                | Slot::Opaque(Opacity::Unfocused(refusal)) => Some((declared.name, refusal)),
                | Slot::Defined(_) | Slot::Opaque(Opacity::Owed | Opacity::Refused) => None,
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
    ///   on a fresh machine: its value is returned, and forced when it is a
    ///   thunk; a terminal that is, or holds outside any suspension, a
    ///   declaration owed its body, and a run stuck observing one, is
    ///   [`Evaluation::Blamed`] on it; any other stuck run is
    ///   [`Evaluation::Stuck`]; a machine fault or a terminal with no core
    ///   reading is [`Evaluation::Unfinished`]; otherwise the terminal is read
    ///   back and spelled: an integer in decimal, a text quoted with its
    ///   escapes, `()`, a pair as `(a, b)`, an injection as `inl(v)` or
    ///   `inr(v)`, a thunk as `<thunk>`, a function as `<fun>`, a code as
    ///   `<code>`.
    /// - provides: the run stage every caller shares, so one declaration has
    ///   one outcome and one spelling wherever it is run.
    /// - fails: never; every failure is an outcome. A refused entry command
    ///   also produces `Unrunnable`; its attempted focusing may already have
    ///   appended command-arena nodes.
    /// - panics: none.
    /// - intension: each run is bounded by a step budget; the reference walk,
    ///   the readback and the spelling are recursion-free, their pending work
    ///   explicit stacks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one source per outcome class the fragment can write
    ///   and per spelling arm it can reach, each run asserted at its exact
    ///   evaluation; a goal met directly, through a force and through an
    ///   application; a refused and a code reference reached directly and
    ///   through another declaration. Machine exhaustion and every core
    ///   spelling constructor are not generated by the source cases; structured
    ///   terminals have separate core-to-machine and spelling witnesses.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::each_outcome_class_has_its_status`
    /// - witness: `evaluate::tests::a_constructed_terminal_blames_its_first_opaque_field`
    /// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
    #[anodized::spec(
        captures: [declarations = self.declarations.len(), definitions = self.definitions.len(),
            watermark = self.arena.watermark(), blocked = match self.declarations.get(usize::from(constant)) {
                None => Some(Unrunnable::Undeclared(constant)),
                Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) }) => Some(Unrunnable::Refused(name)),
                Some(&Declared { name, slot: Slot::Opaque(Opacity::Unfocused(refusal)) }) =>
                    Some(Unrunnable::Unfocused { declaration: name, refusal }),
                Some(&Declared { slot: Slot::Defined(_) | Slot::Opaque(Opacity::Owed), .. }) => None,
            }],
        ensures: |ref ret| self.declarations.len() == declarations && self.definitions.len() == definitions
            && blocked.is_none_or(|reason| matches!(*ret, Evaluation::Unrunnable(actual) if actual == reason)
                && self.arena.watermark() == watermark)
            && match *ret {
                Evaluation::Blamed(name) => self.declarations.iter().any(|declared|
                    declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Owed))),
                Evaluation::Unrunnable(Unrunnable::Undeclared(index)) => usize::from(index) >= declarations,
                Evaluation::Unrunnable(Unrunnable::Refused(name)) => self.declarations.iter().any(|declared|
                    declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Refused))),
                Evaluation::Unrunnable(Unrunnable::Unfocused { declaration, .. }) =>
                    self.declarations.iter().any(|declared| declared.name == declaration),
                Evaluation::Unfinished(Unfinished::Inconsistent(index)) => self.declarations.get(usize::from(index))
                    .is_some_and(|declared| matches!(declared.slot, Slot::Defined(_))),
                Evaluation::Value(_) | Evaluation::Stuck(_)
                    | Evaluation::Unfinished(Unfinished::Fault(_) | Unfinished::Readback(_)) => true,
            }
    )]
    #[inline]
    pub fn evaluate(
        &mut self,
        constant: ConstantIndex,
    ) -> Evaluation<'source>
    {
        if let Maybe::Present(unrunnable) = self.unrunnable(constant) {
            return Evaluation::Unrunnable(unrunnable);
        }
        let (returned, forced) = match self.entries(constant) {
            | Ok(entries) => entries,
            | Err(refusal) => {
                return Evaluation::Unrunnable(match self.name(constant) {
                    | Maybe::Present(declaration) => Unrunnable::Unfocused {
                        declaration,
                        refusal,
                    },
                    | Maybe::Absent(declaration_name::Absent::Undeclared) => {
                        Unrunnable::Undeclared(constant)
                    },
                });
            },
        };
        let budget = StepCount::from(RUN_BUDGET);
        let mut machine = Machine::new(&self.arena, &self.definitions);
        let returned = match machine.run(returned, budget) {
            | Ok(outcome) => outcome,
            | Err(fault) => return Evaluation::Unfinished(Unfinished::Fault(fault)),
        };
        let terminal = match self.halted(&machine, returned) {
            | Ok(value) => value,
            | Err(evaluation) => return evaluation,
        };
        let terminal = match machine.store().value(terminal) {
            | Some(&HeapValue::Thunk { .. }) => {
                let forced = match machine.run(forced, budget) {
                    | Ok(outcome) => outcome,
                    | Err(fault) => return Evaluation::Unfinished(Unfinished::Fault(fault)),
                };
                match self.halted(&machine, forced) {
                    | Ok(value) => value,
                    | Err(evaluation) => return evaluation,
                }
            },
            | Some(
                &(HeapValue::Literal(_)
                | HeapValue::Constructed { .. }
                | HeapValue::Closure { .. }
                | HeapValue::Opaque(_)),
            )
            | None => terminal,
        };
        let mut core = CoreArena::new();
        match machine.read_back(terminal, &mut core) {
            | Ok(read) => Evaluation::Value(self.spell(&core, read)),
            | Err(refusal) => Evaluation::Unfinished(Unfinished::Readback(refusal)),
        }
    }

    /// The first declaration reachable from `constant` through references
    /// that the machine cannot carry, as the reason it never runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first reached absent, refused or unfocused declaration is
    ///   returned with its exact identity; an owed declaration is carried.
    ///   Absence means the reachable reference graph contains no such obstacle.
    /// - fails: an undeclared reference reports its own index, not the run
    ///   target.
    /// - panics: none.
    /// - intension: each declared position is expanded at most once, including
    ///   when references repeat or form a cycle.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct and transitive refusal and code references are
    ///   blocked, while owed references reach the machine; cycles are not built
    ///   by these admitted source fixtures.
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    #[anodized::spec(ensures: |ret| {
        let root = match self.declarations.get(usize::from(constant)) {
            None => ret == Maybe::Present(Unrunnable::Undeclared(constant)),
            Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) }) => ret == Maybe::Present(Unrunnable::Refused(name)),
            Some(&Declared { name, slot: Slot::Opaque(Opacity::Unfocused(refusal)) }) =>
                ret == Maybe::Present(Unrunnable::Unfocused { declaration: name, refusal }),
            Some(&Declared { slot: Slot::Opaque(Opacity::Owed), .. }) => matches!(ret, Maybe::Absent(carried::Absent::Carried)),
            Some(&Declared { slot: Slot::Defined(_), .. }) => true,
        };
        root && match ret {
            Maybe::Present(Unrunnable::Undeclared(index)) => self.declarations.get(usize::from(index)).is_none(),
            Maybe::Present(Unrunnable::Refused(name)) => self.declarations.iter().any(|declared|
                declared.name == name && matches!(declared.slot, Slot::Opaque(Opacity::Refused))),
            Maybe::Present(Unrunnable::Unfocused { declaration, refusal }) => self.declarations.iter().any(|declared|
                declared.name == declaration && matches!(declared.slot, Slot::Opaque(Opacity::Unfocused(actual)) if actual == refusal)),
            Maybe::Absent(carried::Absent::Carried) => true,
        }
    })]
    fn unrunnable(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<Unrunnable<'source>, carried::Absent>
    {
        let mut seen = vec![false; self.declarations.len()];
        let mut pending = Vec::from([constant]);
        while let Some(reached) = pending.pop() {
            let position = usize::from(reached);
            let Some(declared) = self.declarations.get(position)
            else {
                return Maybe::Present(Unrunnable::Undeclared(reached));
            };
            match seen.get_mut(position) {
                | Some(visited) if !*visited => *visited = true,
                | Some(_) | None => continue,
            }
            match declared.slot {
                | Slot::Defined(ref referred) => pending.extend(referred.iter().copied()),
                | Slot::Opaque(Opacity::Owed) => {},
                | Slot::Opaque(Opacity::Refused) => {
                    return Maybe::Present(Unrunnable::Refused(declared.name));
                },
                | Slot::Opaque(Opacity::Unfocused(refusal)) => {
                    return Maybe::Present(Unrunnable::Unfocused {
                        declaration: declared.name,
                        refusal,
                    });
                },
            }
        }
        Maybe::Absent(carried::Absent::Carried)
    }

    /// The two commands a run of `constant` needs: `return c`, and `force c`
    /// for a constant whose value is a thunk.
    ///
    /// # Specification
    /// - requires: nothing; the constant need not have a definition yet.
    /// - ensures: success returns distinct, allocated return and force commands
    ///   for the same constant, in that order, in this program's arena.
    /// - fails: preserves the focusing refusal; nodes already appended are not
    ///   rolled back when a later allocation fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordinary value runs through the return entry and a
    ///   thunk through both entries; allocation exhaustion is not forced.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    #[anodized::spec(ensures: |ret| match ret {
        Ok((returned, forced)) => returned != forced && self.arena.command(returned).is_some()
            && self.arena.command(forced).is_some(),
        Err(_) => true,
    })]
    /// # Errors
    /// The [`FocusRefusal`] of a command arena that refused a node.
    fn entries(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<(CommandId, CommandId), FocusRefusal>
    {
        let mut core = CoreArena::new();
        let value = core.value_constant(constant);
        let returned = core.computation_return(value);
        let forced = core.computation_force(value);
        let mut provenance = Provenance::new();
        Ok((
            focus_computation(&core, returned, &mut self.arena, &mut provenance)?,
            focus_computation(&core, forced, &mut self.arena, &mut provenance)?,
        ))
    }

    /// The value `outcome` halted with, or the evaluation it ends the run
    /// with: blame on a declaration owed its body met at the terminal or by an
    /// observation, and the stuck state otherwise.
    ///
    /// # Specification
    /// - requires: `outcome` was produced by `machine`; a halted id resolves in
    ///   its store.
    /// - ensures: success returns the identical halted id, never an immediately
    ///   opaque value. A stuck result retains its precise stuck reason; opacity
    ///   reached outside suspension is instead classified by declaration
    ///   standing.
    /// - fails: returns blame, unrunnability or inconsistency for an opaque
    ///   declaration, or the unchanged stuck outcome; it never spells a value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct, forced and applied goals preserve blame,
    ///   while a constructed terminal selects its first opaque field and an
    ///   unforced suspension does not expose its goal; other stuck reasons are
    ///   not separately generated by these source and core fixtures.
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_constructed_terminal_blames_its_first_opaque_field`
    #[anodized::spec(
        requires: match outcome { Outcome::Halted(value) => machine.store().value(value).is_some(), Outcome::Stuck(_) => true },
        captures: [halted = match outcome { Outcome::Halted(value) => Some(value), Outcome::Stuck(_) => None },
            stuck = match outcome { Outcome::Stuck(ref reason) => Some(core::mem::discriminant(reason)), Outcome::Halted(_) => None }],
        ensures: |ref ret| match *ret {
            Ok(value) => halted == Some(value)
                && !matches!(machine.store().value(value), Some(&HeapValue::Opaque(_))),
            Err(Evaluation::Stuck(ref actual)) => stuck == Some(core::mem::discriminant(actual)),
            Err(Evaluation::Value(_)) => false,
            Err(Evaluation::Blamed(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_)) => true,
        }
    )]
    /// # Errors
    /// The evaluation a run ends with when it halted on, or stuck at, an
    /// opaque constant, or stuck otherwise.
    fn halted(
        &self,
        machine: &Machine<'_>,
        outcome: Outcome,
    ) -> Result<HeapValueId, Evaluation<'source>>
    {
        match outcome {
            | Outcome::Halted(value) => match Self::opaque_within(machine, value) {
                | Maybe::Present(constant) => Err(self.met(constant)),
                | Maybe::Absent(carried::Absent::Carried) => Ok(value),
            },
            | Outcome::Stuck(stuck) => {
                let observed = match stuck {
                    | Stuck::Unobservable { value, .. } | Stuck::Unmatched { value, .. } => {
                        machine.store().value(value)
                    },
                    | Stuck::UnboundVariable { .. }
                    | Stuck::UnboundCovariable(_)
                    | Stuck::UndefinedConstant(_)
                    | Stuck::CyclicConstant(_)
                    | Stuck::IllFormedCommand(_)
                    | Stuck::IllFormedProducer(_)
                    | Stuck::IllFormedConsumer(_) => None,
                };
                match observed {
                    | Some(&HeapValue::Opaque(constant)) => Err(self.met(constant)),
                    | Some(
                        &(HeapValue::Literal(_)
                        | HeapValue::Constructed { .. }
                        | HeapValue::Thunk { .. }
                        | HeapValue::Closure { .. }),
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
    #[anodized::spec(ensures: |ret| match machine.store().value(value) {
        Some(&HeapValue::Opaque(constant)) => ret == Maybe::Present(constant),
        Some(&HeapValue::Constructed { .. }) => true,
        Some(&(HeapValue::Literal(_) | HeapValue::Thunk { .. } | HeapValue::Closure { .. })) | None =>
            matches!(ret, Maybe::Absent(carried::Absent::Carried)),
    })]
    fn opaque_within(
        machine: &Machine<'_>,
        value: HeapValueId,
    ) -> Maybe<ConstantIndex, carried::Absent>
    {
        let mut pending = Vec::from([value]);
        while let Some(id) = pending.pop() {
            match machine.store().value(id) {
                | Some(&HeapValue::Opaque(constant)) => return Maybe::Present(constant),
                | Some(&HeapValue::Constructed { ref fields, .. }) => {
                    pending.extend(fields.iter().rev().copied());
                },
                | Some(
                    &(HeapValue::Literal(_) | HeapValue::Thunk { .. } | HeapValue::Closure { .. }),
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
    /// - ensures: owed positions blame their name, refused and unfocused ones
    ///   remain unrunnable with their identity, a defined position is
    ///   inconsistent, and an absent position reports that exact undeclared
    ///   index.
    /// - fails: every classification is an evaluation, never a panic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real composed declarations exercise every standing,
    ///   including the inconsistent defined and out-of-range boundaries.
    /// - witness: `evaluate::tests::terminal_classification_preserves_declaration_identity`
    #[anodized::spec(ensures: |ref ret| match self.declarations.get(usize::from(constant)) {
        Some(&Declared { name, slot: Slot::Opaque(Opacity::Owed) }) => matches!(*ret, Evaluation::Blamed(actual) if actual == name),
        Some(&Declared { name, slot: Slot::Opaque(Opacity::Refused) }) => matches!(*ret, Evaluation::Unrunnable(Unrunnable::Refused(actual)) if actual == name),
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
        match self.declarations.get(usize::from(constant)) {
            | Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Owed),
            }) => Evaluation::Blamed(name),
            | Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Refused),
            }) => Evaluation::Unrunnable(Unrunnable::Refused(name)),
            | Some(&Declared {
                name,
                slot: Slot::Opaque(Opacity::Unfocused(refusal)),
            }) => Evaluation::Unrunnable(Unrunnable::Unfocused {
                declaration: name,
                refusal,
            }),
            | Some(&Declared {
                slot: Slot::Defined(_),
                ..
            }) => Evaluation::Unfinished(Unfinished::Inconsistent(constant)),
            | None => Evaluation::Unrunnable(Unrunnable::Undeclared(constant)),
        }
    }

    /// The spelling of the terminal `read`, read back into `core`.
    ///
    /// # Specification
    /// - requires: the reachable core graph is finite and acyclic; missing ids
    ///   are permitted and have explicit placeholder spellings.
    /// - ensures: literals retain signs, decimal components and escaped text;
    ///   unit, functions, suspensions and codes have their declared spellings.
    ///   Pairs and injections preserve field order and nesting, lifts are
    ///   erased, and constants retain known names or the unknown-constant
    ///   placeholder.
    /// - fails: unsupported computation heads and missing nodes are spelled,
    ///   not dereferenced or silently omitted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source values cover integer, quoted text, unit,
    ///   functions and thunks; a core fixture covers nested pairs, both
    ///   injection sides and constant names. Numeric and malformed-core cases
    ///   are not separately generated by these witnesses.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
    #[anodized::spec(ensures: |ref ret| match core.computation(read) {
        Some(&Computation::Lambda(_)) => ret.0 == "<fun>",
        Some(&Computation::Return(value)) => match core.value(value) {
            Some(&Value::Unit) => ret.0 == "()",
            Some(&Value::Thunk(_)) => ret.0 == "<thunk>",
            Some(&(Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..))) => ret.0 == "<code>",
            Some(&Value::Constant(constant)) => match self.name(constant) {
                Maybe::Present(name) => ret.0 == name.as_ref(),
                Maybe::Absent(declaration_name::Absent::Undeclared) => ret.0 == "<constant>",
            },
            Some(&Value::Variable { .. }) => ret.0 == "<variable>",
            Some(&Value::Literal(Literal::Integer(ref integer))) => {
                let digits: &str = integer.magnitude().as_ref();
                ret.0.chars().eq(core::iter::once('-').filter(|_| integer.sign() == Sign::Negative).chain(digits.chars()))
            },
            Some(&Value::Literal(Literal::Numeric(ref numeric))) => {
                let integer: &str = numeric.integer_part().as_ref();
                let fraction: &str = numeric.fraction().as_ref();
                ret.0.chars().eq(core::iter::once('-').filter(|_| numeric.sign() == Sign::Negative)
                    .chain(integer.chars()).chain(core::iter::once('.'))
                    .chain(if fraction.is_empty() { "0" } else { fraction }.chars()))
            },
            Some(&Value::Literal(Literal::Text(ref text))) => {
                let text: &str = text.as_ref();
                ret.0.chars().eq(core::iter::once('"').chain(text.escape_debug()).chain(core::iter::once('"')))
            },
            Some(&Value::Pair(..)) => ret.0.starts_with('(') && ret.0.ends_with(')'),
            Some(&Value::Injection(side, _)) => ret.0.starts_with(match side { Side::Left => "inl(", Side::Right => "inr(" }) && ret.0.ends_with(')'),
            Some(&Value::Lift { .. }) => true,
            None => ret.0 == "<dangling>",
        },
        Some(&(Computation::Application(..) | Computation::Bind(..) | Computation::Force(_) | Computation::Case { .. })) | None => ret.0 == "<computation>",
    })]
    fn spell(
        &self,
        core: &CoreArena,
        read: ComputationId,
    ) -> ValueSpelling
    {
        let mut spelled = String::new();
        let mut pending = match core.computation(read) {
            | Some(&Computation::Return(value)) => Vec::from([Piece::Value(value)]),
            | Some(&Computation::Lambda(_)) => Vec::from([Piece::Text("<fun>")]),
            | Some(
                &(Computation::Application(..)
                | Computation::Bind(..)
                | Computation::Force(_)
                | Computation::Case { .. }),
            )
            | None => Vec::from([Piece::Text("<computation>")]),
        };
        while let Some(piece) = pending.pop() {
            let value = match piece {
                | Piece::Text(text) => {
                    spelled.push_str(text);
                    continue;
                },
                | Piece::Value(value) => value,
            };
            match core.value(value) {
                | Some(&Value::Literal(Literal::Integer(ref integer))) => {
                    if integer.sign() == Sign::Negative {
                        spelled.push('-');
                    }
                    spelled.push_str(integer.magnitude().as_ref());
                },
                | Some(&Value::Literal(Literal::Numeric(ref numeric))) => {
                    if numeric.sign() == Sign::Negative {
                        spelled.push('-');
                    }
                    spelled.push_str(numeric.integer_part().as_ref());
                    spelled.push('.');
                    let fraction: &str = numeric.fraction().as_ref();
                    spelled.push_str(if fraction.is_empty() { "0" } else { fraction });
                },
                | Some(&Value::Literal(Literal::Text(ref text))) => {
                    spelled.push('"');
                    let text: &str = text.as_ref();
                    spelled.extend(text.escape_debug());
                    spelled.push('"');
                },
                | Some(&Value::Unit) => spelled.push_str("()"),
                | Some(&Value::Pair(first, second)) => pending.extend([
                    Piece::Text(")"),
                    Piece::Value(second),
                    Piece::Text(", "),
                    Piece::Value(first),
                    Piece::Text("("),
                ]),
                | Some(&Value::Injection(side, body)) => pending.extend([
                    Piece::Text(")"),
                    Piece::Value(body),
                    Piece::Text(match side {
                        | Side::Left => "inl(",
                        | Side::Right => "inr(",
                    }),
                ]),
                | Some(&Value::Lift { body, .. }) => pending.push(Piece::Value(body)),
                | Some(&Value::Thunk(_)) => spelled.push_str("<thunk>"),
                | Some(
                    &(Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)),
                ) => {
                    spelled.push_str("<code>");
                },
                | Some(&Value::Constant(constant)) => match self.name(constant) {
                    | Maybe::Present(name) => spelled.push_str(name.as_ref()),
                    | Maybe::Absent(declaration_name::Absent::Undeclared) => {
                        spelled.push_str("<constant>");
                    },
                },
                | Some(&Value::Variable { .. }) => spelled.push_str("<variable>"),
                | None => spelled.push_str("<dangling>"),
            }
        }
        ValueSpelling(spelled)
    }
}

impl Runner for Program<'_>
{
    /// Spells the outcome of running the declaration at `constant`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling
    {
        RunSpelling::from(self.evaluate(constant).to_string())
    }
}

/// A piece of a spelling still to write.
#[derive(Clone, Copy, Debug)]
enum Piece
{
    /// Fixed text.
    Text(&'static str),
    /// A value, spelled in turn.
    Value(ValueId),
}

/// The constants `body` refers to, outside its types.
///
/// # Specification
/// - requires: the reachable term graph is finite and acyclic; missing ids are
///   ignored rather than followed.
/// - ensures: one index per reference occurrence, preserving multiplicity;
///   quoted types and static code do not contribute references. A constant root
///   contributes only itself and an atomic non-reference root contributes none.
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
#[anodized::spec(ensures: |ref ret| match core.value(body) {
    Some(&Value::Constant(constant)) => ret.iter().copied().eq([constant]),
    Some(&(Value::Variable { .. } | Value::Unit | Value::Literal(_) | Value::Quote(_)
        | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..))) | None => ret.is_empty(),
    Some(&(Value::Pair(..) | Value::Injection(..) | Value::Lift { .. } | Value::Thunk(_))) => true,
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
            | Node::Value(id) => match core.value(id) {
                | Some(&Value::Constant(constant)) => referred.push(constant),
                | Some(&Value::Pair(first, second)) => {
                    pending.extend([Node::Value(first), Node::Value(second)]);
                },
                | Some(&(Value::Injection(_, inner) | Value::Lift { body: inner, .. })) => {
                    pending.push(Node::Value(inner));
                },
                | Some(&Value::Thunk(computation)) => pending.push(Node::Computation(computation)),
                | Some(
                    &(Value::Variable { .. }
                    | Value::Unit
                    | Value::Literal(_)
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)),
                )
                | None => {},
            },
            | Node::Computation(id) => match core.computation(id) {
                | Some(&Computation::Lambda(inner)) => pending.push(Node::Computation(inner)),
                | Some(&Computation::Application(head, argument)) => {
                    pending.extend([Node::Computation(head), Node::Value(argument)]);
                },
                | Some(&(Computation::Return(value) | Computation::Force(value))) => {
                    pending.push(Node::Value(value));
                },
                | Some(&Computation::Bind(bound, rest)) => {
                    pending.extend([Node::Computation(bound), Node::Computation(rest)]);
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => pending.extend([
                    Node::Value(scrutinee),
                    Node::Computation(on_left),
                    Node::Computation(on_right),
                ]),
                | None => {},
            },
        }
    }
    referred
}

#[cfg(test)]
mod tests
{
    use gandr_core_sequent::FocusRefusal;
    use gandr_core_sequent::MachineFault;
    use gandr_core_sequent::Stuck;
    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Evaluation;
    use super::Program;
    use super::RunStatus;
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
    /// - ensures: definitions and declared names occupy the same dense table.
    /// - panics: if the grammar or composition premise fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values, goals, refusals, later definitions of
    ///   existing names and an empty source have independent expected outcomes
    ///   or targets.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::the_run_target_is_the_last_name_declared`
    #[anodized::spec(ensures: |ref ret| usize::from(ret.definitions.len()) == ret.declarations.len())]
    fn program<'source>(source: impl Into<SourceText<'source>>) -> Program<'source>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        match compose(&grammar, CorpusRoot::Fixture, source.into(), &mut lowerings) {
            | Ok(Composed::Settled { program, .. }) => program,
            | Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            | Err(fault) => panic!("faulted: {fault}"),
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
    #[anodized::spec(
        requires: program.declarations.iter().any(|declared| declared.name == name),
        captures: [declarations = program.declarations.len()],
        ensures: |ref ret| program.declarations.len() == declarations
            && match *ret { Evaluation::Unrunnable(Unrunnable::Undeclared(index)) => usize::from(index) >= declarations, _ => true }
    )]
    fn run<'source>(
        program: &mut Program<'source>,
        name: SurfaceName<'source>,
    ) -> Evaluation<'source>
    {
        let position = program
            .declarations
            .iter()
            .position(|declared| declared.name == name)
            .expect("the program declares the name");
        program.evaluate(ConstantIndex::from(position))
    }

    #[test]
    fn a_value_runs_to_its_spelling()
    {
        let mut values = program(
            r#"def answer : Integer ; def answer = 42 ;
def greeting : String ; def greeting = "a \"quoted\"\nline" ;
def nothing : Unit ; def nothing = () ;
def copy = answer ;
def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { ret x } } ;
def first : +U (Integer -> Integer -> -F Integer) ; def first = thunk { fn (x) { fn (y) { ret x } } } ;
def applied : +U (-F Integer) ; def applied = thunk { (force identity)(answer) } ;
def chosen : +U (-F Integer) ; def chosen = thunk { ((force first)(answer))(7) } ;
def delayed : +U (-F String) ; def delayed = thunk { ret "later" } ;
def nested : +U (-F (+U (-F Integer))) ; def nested = thunk { ret thunk { ret 1 } } ;"#,
        );
        for (name, spelled) in [
            ("answer", "42"),
            ("greeting", r#""a \"quoted\"\nline""#),
            ("nothing", "()"),
            ("copy", "42"),
            ("identity", "<fun>"),
            ("first", "<fun>"),
            ("applied", "42"),
            ("chosen", "42"),
            ("delayed", r#""later""#),
            ("nested", "<thunk>"),
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

    #[test]
    fn a_run_reaching_a_goal_blames_it()
    {
        let mut goals = program(
            r#"def later : Integer ;
def copy : Integer ; def copy = later ;
def suspended : +U (-F Integer) ;
def forced : +U (-F Integer) ; def forced = thunk { force suspended } ;
def function : +U (Integer -> -F Integer) ;
def applied : +U (-F Integer) ; def applied = thunk { (force function)(1) } ;
def untouched : +U (-F Integer) ; def untouched = thunk { ret 3 } ;
def holder : +U (-F Integer) ; def holder = thunk { force suspended } ;
def kept : +U (-F (+U (-F Integer))) ; def kept = thunk { ret holder } ;"#,
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
            "<thunk>",
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
def small : Type ; def small = Integer ;
def alias : Type ; def alias = small ;
def again : Type ; def again = alias ;
def later : Integer ; def lost = missing ; def answer = 42 ;
def wide : Type ; def wide = String ;"#,
        );
        let before = carried.arena.watermark();
        assert!(
            carried
                .focus_refusals()
                .map(|(name, _)| name)
                .eq([SurfaceName::from("small"), SurfaceName::from("wide")])
        );
        for name in ["bad", "uses"] {
            assert_eq!(
                run(&mut carried, SurfaceName::from(name)),
                Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("bad"))),
                "`{name}` reaches the refused declaration and never runs"
            );
        }
        for name in ["small", "alias", "again"] {
            let evaluation = run(&mut carried, SurfaceName::from(name));
            assert!(
                matches!(
                    evaluation,
                    Evaluation::Unrunnable(Unrunnable::Unfocused {
                        declaration,
                        refusal: FocusRefusal::Code(_),
                    }) if declaration == SurfaceName::from("small")
                ),
                "`{name}` reaches the code and never runs: {evaluation}"
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
    fn each_outcome_class_has_its_status()
    {
        let mut written = program(
            r#"def later : Integer ; def answer = 42 ; def copy : Integer ; def copy = later ;
def small : Type ; def small = Integer ;"#,
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
                run(&mut written, SurfaceName::from("small")),
                RunStatus::Unreached,
            ),
            (
                Evaluation::Stuck(Stuck::UndefinedConstant(ConstantIndex::from(0_usize))),
                RunStatus::Failed,
            ),
            (
                Evaluation::Unfinished(Unfinished::Fault(MachineFault::OutOfSteps)),
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
    #[test]
    fn terminal_classification_preserves_declaration_identity()
    {
        let written = program(
            r#"def answer = 42 ; def later : Integer ;
def bad : Integer ; def bad = "text" ; def small : Type ; def small = Integer ;"#,
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
            Unrunnable::Unfocused { declaration, refusal: FocusRefusal::Code(_) }) if declaration == SurfaceName::from("small"))
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
        let nested = core.value_pair(second, first);
        let outer = core.value_pair(unit, nested);
        let returned = core.computation_return(outer);
        let mut commands = gandr_core_sequent::CommandArena::default();
        let mut provenance = gandr_core_sequent::Provenance::new();
        let command =
            gandr_core_sequent::focus_computation(&core, returned, &mut commands, &mut provenance)
                .expect("the constructed terminal focuses");
        let mut machine = gandr_core_sequent::Machine::new(&commands, &goals.definitions);
        let outcome = machine
            .run(command, gandr_core_sequent::StepCount::from(100_usize))
            .expect("the constructed terminal runs");
        assert_eq!(
            goals.halted(&machine, outcome),
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
        let nested = core.value_pair(second, first);
        let outer = core.value_pair(first, nested);
        let mut referred = super::references(&core, outer);
        referred.sort_unstable();
        assert_eq!(referred.as_slice(), &[
            ConstantIndex::from(0_usize),
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize)
        ]);
        let returned = core.computation_return(outer);
        assert_eq!(
            names.spell(&core, returned).as_ref(),
            "(first, (second, first))"
        );
        for (side, expected) in [
            (gandr_kernel_term::Side::Left, "inl(second)"),
            (gandr_kernel_term::Side::Right, "inr(second)"),
        ] {
            let injected = core.value_injection(side, second);
            let returned = core.computation_return(injected);
            assert_eq!(names.spell(&core, returned).as_ref(), expected);
        }
    }

    #[test]
    fn sparse_admission_positions_keep_program_order()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = gandr_surface_parser::parse(
            &grammar,
            SourceText::from("def omitted : Integer ; def answer = 42 ;"),
        )
        .expect("the fixture parses")
        .into_tree();
        let mut core = gandr_core_term::CoreArena::new();
        let lowered = gandr_surface_lowering::lower_module(
            &grammar,
            &tree,
            &mut core,
            gandr_surface_lowering::LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the fixture lowers");
        let answer = *lowered
            .declarations()
            .last()
            .expect("the answer follows the omitted name");
        assert_eq!(answer.constant(), ConstantIndex::from(1_usize));
        let sparse = gandr_surface_lowering::LoweredModule::new(
            Vec::from([answer]),
            Vec::new(),
            lowered.attributes().clone(),
            lowered.origins().clone(),
            gandr_surface_lowering::ModuleImports::default(),
            lowered.recognition().clone(),
        );
        let verdicts = gandr_core_checker::check_module(
            &mut gandr_core_checker::CheckingContext::new(
                &mut core,
                gandr_core_checker::CheckBudget::DEFAULT,
            ),
            &crate::compose::adapt(&sparse),
        );
        let mut program = Program::new(&core, &sparse, &verdicts);
        assert_eq!(
            program.target(),
            Maybe::Present(ConstantIndex::from(0_usize))
        );
        assert_eq!(
            program.name(ConstantIndex::from(0_usize)),
            Maybe::Present(SurfaceName::from("answer"))
        );
        assert!(
            matches!(run(&mut program, SurfaceName::from("answer")), Evaluation::Value(ref value) if value.as_ref() == "42")
        );
    }
}
