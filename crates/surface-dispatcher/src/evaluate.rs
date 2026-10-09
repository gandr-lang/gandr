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
    /// trivial.
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
    ///   over `core`; `module`'s admission positions are dense in declaration
    ///   order, as the lowering mints them.
    /// - ensures: one entry per declaration of `module`, at its admission
    ///   position: a declaration checked or synthesised has its elaborated body
    ///   focused and is defined as it; one owed its body is carried as itself;
    ///   one refused by the lowering or the checker, or whose body does not
    ///   focus, is carried as itself and never run.
    /// - provides: the program every run of the module's declarations shares.
    /// - fails: never; a body that does not focus is the declaration's
    ///   standing, not a failure of the program.
    /// - panics: none.
    /// - intension: one focusing per accepted declaration; nothing runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sources holding an accepted, an owed, a refused and
    ///   an unfocusable declaration are built and each run asserted at its
    ///   exact outcome, which only the standing built for it gives.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
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
    /// trivial.
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
    /// trivial.
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
    /// - fails: never; every failure is an outcome.
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
    ///   through another declaration.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::each_outcome_class_has_its_status`
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
    /// trivial.
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
    /// trivial.
    ///
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
    /// trivial.
    ///
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
                | Some(&(Value::Quote(_) | Value::QuoteComputation(_))) => {
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
/// trivial.
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
                    | Value::QuoteComputation(_)),
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
    ///
    /// trivial.
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
    ///
    /// trivial.
    fn run<'source>(
        program: &mut Program<'source>,
        name: impl Into<SurfaceName<'source>>,
    ) -> Evaluation<'source>
    {
        let name = name.into();
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
            let evaluation = run(&mut values, name);
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
                run(&mut goals, name),
                Evaluation::Blamed(SurfaceName::from(goal)),
                "`{name}` is blamed on the goal it reaches"
            );
        }
        assert_eq!(
            run(&mut goals, "untouched").to_string(),
            "3",
            "a run that reaches no goal is not blamed for one beside it"
        );
        assert_eq!(
            run(&mut goals, "kept").to_string(),
            "<thunk>",
            "a goal under a suspension the run returns is not reached"
        );
        assert_eq!(
            run(&mut goals, "forced").to_string(),
            "blame: `suspended` is owed its body",
            "blame is spelled with the goal it names"
        );
    }

    #[test]
    fn a_reference_the_machine_cannot_carry_is_never_run()
    {
        let mut carried = program(
            r#"def bad : Integer ; def bad = "text" ;
def uses : Integer ; def uses = bad ;
def small : Type ; def small = Integer ;
def alias : Type ; def alias = small ;
def again : Type ; def again = alias ;"#,
        );
        for name in ["bad", "uses"] {
            assert_eq!(
                run(&mut carried, name),
                Evaluation::Unrunnable(Unrunnable::Refused(SurfaceName::from("bad"))),
                "`{name}` reaches the refused declaration and never runs"
            );
        }
        for name in ["small", "alias", "again"] {
            let evaluation = run(&mut carried, name);
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
    }

    #[test]
    fn each_outcome_class_has_its_status()
    {
        let mut written = program(
            r#"def later : Integer ; def answer = 42 ; def copy : Integer ; def copy = later ;
def small : Type ; def small = Integer ;"#,
        );
        let rows = [
            (run(&mut written, "answer"), RunStatus::Value),
            (run(&mut written, "copy"), RunStatus::Failed),
            (run(&mut written, "small"), RunStatus::Unreached),
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
        let none = program(r#"// nothing declared"#);
        assert_eq!(
            none.target(),
            Maybe::Absent(run_target::Absent::NoDeclaration),
            "a source of no name has no target"
        );
    }
}
