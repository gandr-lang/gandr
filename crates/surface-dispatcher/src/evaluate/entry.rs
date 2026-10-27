//! A program's entry run: the `main` its source declares at the top level,
//! forced, applied to the arguments when it reads them, its integer the
//! process's exit status, or zero when it returns the unit.
//!
//! The run takes a host. An operation no handler of the run claims is offered
//! to it: `Proc.exit` stops the run with its payload as the exit status,
//! `Console.print` writes its line to the run's [`Console`], a `Net`
//! operation goes to the run's network when it has one, and every other
//! operation is declined, so the run is stuck at it and reported as any stuck
//! run is.

use alloc::string::String;

use anodized::spec;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Verdict;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::focus_computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::effect::host::PROC;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::evaluate_with_host;
use gandr_runtime_net::Net;
use gandr_surface_lowering::Arguments;
use gandr_surface_lowering::Container;
use gandr_surface_lowering::ENTRY;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::entry_shape;
use quenchant_shape::shape::Maybe;

use super::Console;
use super::Evaluation;
use super::Program;
use super::RUN_BUDGET;
use super::Start;
use super::Unfinished;
use super::console;
use super::net;

/// The operation of [`PROC`] that ends the process.
const EXIT: &str = "exit";

/// The declaration a program starts at, and what it takes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Entry
{
    /// The entry's admission position.
    pub constant: ConstantIndex,
    /// Whether it reads the program's arguments.
    pub arguments: Arguments,
}

/// The status a process leaves with: the low eight bits of the integer an
/// entry returns or exits with, as a POSIX `exit` keeps them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExitStatus(u8);

impl From<ExitStatus> for u8
{
    /// The status's byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(status: ExitStatus) -> Self
    {
        status.0
    }
}

impl From<u8> for ExitStatus
{
    /// The status of the byte `code`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(code: u8) -> Self
    {
        Self(code)
    }
}

impl From<&IntegerLiteral> for ExitStatus
{
    /// The low eight bits of `literal`, read in two's complement, so `-1` is
    /// `255` and `256` is `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the integer modulo 256, taken non-negative.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, a small code, 255, 256, a long magnitude and a
    ///   negative integer.
    /// - witness: `evaluate::entry::tests::an_exit_status_keeps_the_low_byte_1881`
    #[spec(
        captures: [odd = literal.magnitude().as_ref().bytes().last().is_some_and(|digit| digit % 2 == 1)],
        ensures: |ret| (ret.0 % 2 == 1) == odd,
    )]
    #[inline]
    fn from(literal: &IntegerLiteral) -> Self
    {
        let residue = literal
            .magnitude()
            .as_ref()
            .bytes()
            .fold(0_u16, |held, digit| {
                held.saturating_mul(10)
                    .saturating_add(u16::from(digit.saturating_sub(b'0')))
                    .rem_euclid(256)
            });
        let residue = match literal.sign() {
            Sign::NonNegative => residue,
            Sign::Negative => 256_u16.saturating_sub(residue).rem_euclid(256),
        };
        Self(u8::try_from(residue).unwrap_or(u8::MAX))
    }
}

/// What running a program's entry came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Entered<'source>
{
    /// The entry returned an integer, or exited with one.
    Exited(ExitStatus),
    /// The run ended short of an exit status: unrunnable, blamed, stuck at a
    /// hole or elsewhere, or unfinished, or it returned no integer.
    Ended(Evaluation<'source>),
}

/// The host of an entry run: `Proc.exit` ends it, `Console.print` writes to
/// its console, a `Net` operation goes to its network when it has one, and
/// nothing else is served.
struct EntryHost<'host>
{
    /// Where the run's printed lines go.
    console: &'host mut dyn Console,
    /// The run's network, when it has one.
    net: Option<&'host mut Net>,
}

impl HostHandler for EntryHost<'_>
{
    type Abort = ExitStatus;

    /// Stop at `Proc.exit` with its integer payload as the status; write a
    /// `Console.print` line to the console and resume with the unit; serve a
    /// `Net` operation on the network, when the run has one; decline every
    /// other operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        if let Some(reply) = console::served(self.console, request, values) {
            return reply;
        }
        if let Some(network) = self.net.as_deref_mut()
            && let Some(reply) = net::served(network, request, values)
        {
            return reply;
        }
        if request.signature.name().as_ref() != PROC || request.operation.as_ref() != EXIT {
            return HostReply::Decline;
        }
        match values.value(request.payload) {
            Some(&HeapValue::Literal(Literal::Integer(ref code))) => {
                HostReply::Abort(ExitStatus::from(code))
            },
            Some(_) | None => HostReply::Decline,
        }
    }
}

impl<'source> Program<'source>
{
    /// The declaration this program starts at: the `main` its source declares
    /// at the top level, at an entry's type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn entry(&self) -> Maybe<Entry, program_entry::Absent>
    {
        self.entry
    }

    /// Run `entry` with `arguments`, under a host that serves `Proc.exit`,
    /// writes each `Console.print` line to `console`, and serves each `Net`
    /// operation on `net` when it is given.
    ///
    /// # Specification
    /// - requires: nothing; an entry the program cannot run is an outcome.
    /// - ensures: [`Evaluation::Unrunnable`], as [`Self::evaluate`] decides it,
    ///   before any command runs. Otherwise the entry is forced, and, when it
    ///   reads them, applied to [`argument_list`] of `arguments`; each line it
    ///   prints is handed to `console` in order as it runs, and each `Net`
    ///   operation it performs is served on `net`, or declined without one; a
    ///   run that performs `Proc.exit` with an integer, or returns an integer,
    ///   is [`Entered::Exited`] with that integer's low byte, one returning the
    ///   unit is [`Entered::Exited`] with zero, and any other end is
    ///   [`Entered::Ended`] with the evaluation [`Self::evaluate`] gives it,
    ///   [`Evaluation::Holed`] for a hole reached.
    /// - fails: never; every failure is an outcome.
    /// - panics: none.
    /// - executable: none — the run's outcome is the machine's; the witnesses
    ///   observe it through the process.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry returning a code, one counting its
    ///   arguments, one exiting early through `Proc.exit`, one reaching a goal,
    ///   one reaching a hole after a call, one passing a hole a branch never
    ///   reaches, one printing two lines and returning the unit, and one
    ///   pinging an endpoint over the network and printing its answer.
    /// - witness: `evaluate::entry::tests::an_entry_runs_to_its_exit_status_1881`
    /// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
    /// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
    /// - witness: `tests::run::a_script_pings_over_its_network_3186`
    #[inline]
    pub fn enter(
        &mut self,
        entry: Entry,
        arguments: &[String],
        console: &mut dyn Console,
        net: Option<&mut Net>,
    ) -> Entered<'source>
    {
        let constant = entry.constant;
        if let Maybe::Present(unrunnable) = self.unrunnable(constant, Start::Accepted) {
            return Entered::Ended(Evaluation::Unrunnable(unrunnable));
        }
        let mut core = CoreArena::new();
        let value = core.value_constant(constant);
        let forced = core.computation_force(value);
        let root = match entry.arguments {
            Arguments::Unread => forced,
            Arguments::Read => {
                let list = argument_list(&mut core, arguments);
                core.computation_application(forced, list)
            },
        };
        let mut provenance = Provenance::new();
        let command = match focus_computation(&core, root, &mut self.arena, &mut provenance) {
            Ok(command) => command,
            Err(refusal) => {
                return Entered::Ended(Evaluation::Unrunnable(self.unfocused(constant, refusal)));
            },
        };
        let mut store = Store::new();
        let ran = evaluate_with_host(
            &self.arena,
            &self.definitions,
            command,
            (Fuel::from(RUN_BUDGET), &mut store),
            &mut EntryHost { console, net },
        );
        match ran {
            Err(declined) => Entered::Ended(Evaluation::Unfinished(Unfinished::Declined(declined))),
            Ok(HostOutcome::Aborted(status)) => Entered::Exited(status),
            Ok(HostOutcome::Completed(outcome)) => match self.halted(&store, outcome) {
                Err(evaluation) => Entered::Ended(evaluation),
                Ok(terminal) => match store.value(terminal) {
                    Some(&HeapValue::Literal(Literal::Integer(ref code))) => {
                        Entered::Exited(ExitStatus::from(code))
                    },
                    Some(&HeapValue::Constructed {
                        tag: ConstructorTag::Tuple(arity),
                        ..
                    }) if arity == ProducerArity::ZERO => Entered::Exited(ExitStatus::from(0_u8)),
                    Some(_) | None => Entered::Ended(self.finish(constant, &store, terminal)),
                },
            },
        }
    }
}

/// `arguments` as a value of `List(String)`, in their order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cons list whose cells hold `arguments` as string literals,
///   the first argument in the first cell, ending in nil.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — no argument, and three distinct arguments read back in
///   order.
/// - witness: `evaluate::entry::tests::the_arguments_are_a_list_in_their_order_1881`
#[spec(ensures: |ret| matches!(core.value(ret), Some(&Value::ListNil)) == arguments.is_empty())]
fn argument_list(
    core: &mut CoreArena,
    arguments: &[String],
) -> ValueId
{
    let nil = core.value_list_nil();
    arguments.iter().rev().fold(nil, |rest, argument| {
        let text = core.value_literal(Literal::Text(StringLiteral::new(argument.clone())));
        core.value_list_cons(text, rest)
    })
}

/// The entry of the program over `module`: the `main` declared at the top
/// level of its last source, the one run, when the checker took it at an
/// entry's type.
///
/// # Specification
/// - requires: `verdicts` judged `module` over `core`.
/// - ensures: the admission position of the declaration named [`ENTRY`] at the
///   top level of the last source any top-level declaration of `module` stands
///   in — a stray, named by the token it opens with, is none — with the
///   arguments its declared type reads, when its verdict states a type
///   [`entry_shape()`] answers; the undeclared absence otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the module's sources and the verdicts
///   as the body does; the witness observes the entries.
///
/// # Adequacy
/// - hypothesis: L3 — a source declaring `main` of each entry type beside
///   another name, one declaring none, one whose module's member is the only
///   `main`, and one running `main()` after declaring it.
/// - witness: `evaluate::entry::tests::the_entry_is_the_main_of_the_source_run_1881`
pub(super) fn entry_of(
    core: &CoreArena,
    module: &LoweredModule<'_>,
    verdicts: &ModuleReport,
) -> Maybe<Entry, program_entry::Absent>
{
    let undeclared = Maybe::Absent(program_entry::Absent::Undeclared);
    let top = |container: Container| match container {
        Container::TopLevel(source) => Some(source),
        Container::Module(_) => None,
    };
    let Some(run) = module
        .declarations()
        .iter()
        .filter_map(|lowered| top(lowered.container()))
        .max()
    else {
        return undeclared;
    };
    let Some(constant) = module
        .declarations()
        .iter()
        .filter(|lowered| {
            lowered.name().as_ref() == ENTRY
                && lowered.role() != Role::Held
                && top(lowered.container()) == Some(run)
        })
        .map(LoweredDeclaration::constant)
        .next_back()
    else {
        return undeclared;
    };
    let declared = verdicts
        .judged()
        .iter()
        .find(|judged| judged.constant() == constant)
        .and_then(|judged| match judged.verdict() {
            Verdict::Checked { declared, .. } | Verdict::Suspended(declared) => Some(declared.id()),
            Verdict::Synthesised { .. }
            | Verdict::Data
            | Verdict::Owed(_)
            | Verdict::Refused(_) => None,
        });
    match declared.map(|declared| entry_shape(core, declared)) {
        Some(Maybe::Present(arguments)) => Maybe::Present(Entry {
            constant,
            arguments,
        }),
        Some(Maybe::Absent(_)) | None => undeclared,
    }
}

quenchant_shape::reason_enum! {
    /// Why a program has no entry.
    pub mod program_entry {
        /// The program's source declares no `main` at its top level at an
        /// entry's type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `main` stands at the top level of the source run.
            Undeclared,
        }
    }
}

#[cfg(test)]
mod tests;
