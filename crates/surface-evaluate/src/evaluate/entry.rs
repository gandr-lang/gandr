//! A program's entry run: the `main` its source declares at the top level,
//! forced, applied to the arguments when it reads them, its integer the
//! process's exit status, or zero when it returns the unit.
//!
//! The run takes a host. An operation no handler of the run claims is offered
//! to it: `Proc.exit` stops the run with its payload as the exit status,
//! `Console.print` writes its line to the run's [`Console`], a `Net`
//! operation goes to the run's network when it has one, a `Reals` operation
//! goes to the plans and the machines the run holds, a `Rand` operation draws
//! from the entropy source of the operating system, and every other operation
//! is declined, so the run is stuck at it and reported as any stuck run is. A
//! migration goes where the host's world bindings bind its world, or runs in
//! this process when the host has none. A host that runs a migration another
//! host shipped answers its body with the same host (#3546).

use alloc::string::String;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::Store;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::effect::host::PROC;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::Migrated;
use gandr_runtime_emitter::MigrationRequest;
use gandr_runtime_net::Net;
use gandr_surface_dispatcher::Console;
use gandr_surface_dispatcher::Entered;
use gandr_surface_dispatcher::Entry;
use gandr_surface_dispatcher::ExitStatus;
use gandr_surface_dispatcher::RealsProfile;
use gandr_surface_dispatcher::Worlds;
use gandr_surface_lowering::Arguments;
use quenchant_shape::shape::Maybe;

use super::Evaluation;
use super::Machine;
use super::Start;
use super::Unrunnable;
use super::console;
use super::net;
use super::rand;
use super::reals;
use super::reals::Reals;
use super::worlds;

/// The operation of [`PROC`] that ends the process.
const EXIT: &str = "exit";

/// The host of an entry run, and of each migration a host runs for another:
/// `Proc.exit` ends it, `Console.print` writes to its console, a `Net`
/// operation goes to its network when it has one, a `Reals` operation goes to
/// the plans and the machines it holds, a `Rand` operation draws from the
/// entropy source of the operating system, a migration goes where its
/// bindings bind the world when it has them, and nothing else is served.
pub(super) struct EntryHost<'host>
{
    /// Where the run's printed lines go.
    pub(super) console: &'host mut dyn Console,
    /// The run's network, when it has one.
    pub(super) net: Option<&'host mut Net>,
    /// The plans and the machines of exact reals that the run holds.
    pub(super) reals: Reals,
    /// The run's world bindings and the program's names, when it has them.
    pub(super) worlds: Option<(Worlds<'host>, &'host [String])>,
}

impl HostHandler for EntryHost<'_>
{
    type Abort = ExitStatus;

    /// Stop at `Proc.exit` with its integer payload as the status; write a
    /// `Console.print` line to the console and resume with the unit; serve a
    /// `Net` operation on the network, when the run has one; serve a `Reals`
    /// operation on the run's plans and machines; serve a `Rand` operation
    /// from the entropy source; decline every other operation.
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
        if let Some(reply) = reals::served(&mut self.reals, self.console, request, values) {
            return reply;
        }
        if let Some(reply) = rand::served(self.console, request, values) {
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

    /// Run a migration here when the host has no world bindings; otherwise
    /// where they bind its world.
    ///
    /// # Specification
    /// trivial.
    fn migrate(
        &mut self,
        request: MigrationRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> Migrated
    {
        match self.worlds {
            Some(worlds) => worlds::shipped(worlds, self.net.as_deref_mut(), request, values),
            None => Migrated::Here,
        }
    }
}

impl<'source> Machine<'_, 'source>
{
    /// Run `entry` with `arguments`, under a host that serves `Proc.exit`,
    /// writes each `Console.print` line to `console`, serves each `Net`
    /// operation on `net` when it is given, serves each `Reals` operation on
    /// the plans and the machines the run holds under the quotas of `profile`,
    /// serves each `Rand` operation from the entropy source of the operating
    /// system, and runs each migration where `worlds`' bindings bind its world
    /// when it is given.
    ///
    /// # Specification
    /// - requires: nothing; an entry the program cannot run is an outcome.
    /// - ensures: [`Evaluation::Unrunnable`], as [`Self::evaluate`] decides it,
    ///   before any command runs, and [`Unrunnable::UnboundWorld`] naming the
    ///   first world the entry holds a capability for that `worlds`' bindings
    ///   bind to no host. Otherwise the entry is forced, and, when it reads
    ///   them, applied to [`argument_list`] of `arguments`, or, when it takes
    ///   the ambient authority, to a fresh object no handler introduced, so an
    ///   operation exercised through it is offered to the host; each line it
    ///   prints is handed to `console` in order as it runs, each `Net`
    ///   operation it performs is served on `net`, or declined without one,
    ///   each `Reals` operation is served on tables of plans and machines that
    ///   the run owns under `profile`, empty until its first `admit`, each
    ///   `Rand` operation is served from the entropy source, and each migration
    ///   runs where the bindings bind its world, or here without one; a run
    ///   that performs `Proc.exit` with an integer, or returns an integer, is
    ///   [`Entered::Exited`] with that integer's low byte, one returning the
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
    ///   reaches, one printing two lines and returning the unit, one pinging an
    ///   endpoint over the network and printing its answer, and one migrating
    ///   to a world its bindings bind to another endpoint, to one they bind to
    ///   this one, and to one they do not bind.
    /// - witness: `evaluate::entry::tests::an_entry_runs_to_its_exit_status_1881`
    /// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
    /// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
    /// - witness: `evaluate::entry::tests::an_entry_prints_through_its_authority_2970`
    /// - witness: `gandr-surface-dispatcher::tests::run::a_script_pings_over_its_network_3186`
    /// - witness: `gandr-surface-dispatcher::tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    /// - witness: `gandr-surface-dispatcher::tests::run::a_world_bound_to_this_host_runs_here`
    /// - witness: `gandr-surface-dispatcher::tests::run::a_world_no_binding_names_is_refused_before_the_run`
    #[inline]
    pub fn enter(
        &mut self,
        entry: Entry,
        arguments: &[String],
        console: &mut dyn Console,
        (net, worlds, profile): (Option<&mut Net>, Option<Worlds<'_>>, RealsProfile),
    ) -> Entered<'source>
    {
        let constant = entry.constant;
        if let Maybe::Present(unrunnable) = self.unrunnable(constant, Start::Accepted) {
            return Entered::Ended(Evaluation::Unrunnable(unrunnable));
        }
        if let Some(Worlds { bindings, .. }) = worlds
            && let Some(world) = self.unbound(bindings)
            && let Some(declared) = self.declarations.get(&world)
        {
            return Entered::Ended(Evaluation::Unrunnable(Unrunnable::UnboundWorld(
                declared.name,
            )));
        }
        let mut core = CoreArena::new();
        let argument = match entry.arguments {
            Arguments::Unread => None,
            Arguments::Read => Some(argument_list(&mut core, arguments)),
            // The authority is a fresh object no handler of the run
            // introduced, so each operation exercised through it, or
            // through a capability attenuated from it, is the host's.
            Arguments::Authority => Some(core.value_unit()),
        };
        let command = match self.rooted(constant, argument.as_slice(), &mut core) {
            Ok(command) => command,
            Err(evaluation) => return Entered::Ended(evaluation),
        };
        let mut store = Store::new();
        let mut host = EntryHost {
            console,
            net,
            reals: Reals::new(profile),
            worlds: worlds.map(|worlds| (worlds, self.names.as_slice())),
        };
        match self.hosted(command, &mut store, &mut host) {
            Err(status) => Entered::Exited(status),
            Ok(Err(evaluation)) => Entered::Ended(evaluation),
            Ok(Ok(terminal)) => match store.value(terminal) {
                Some(&HeapValue::Literal(Literal::Integer(ref code))) => {
                    Entered::Exited(ExitStatus::from(code))
                },
                Some(&HeapValue::Constructed {
                    tag: ConstructorTag::Tuple(arity),
                    ..
                }) if arity == ProducerArity::ZERO => Entered::Exited(ExitStatus::from(0_u8)),
                Some(_) | None => Entered::Ended(self.finish(constant, &store, terminal)),
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

#[cfg(test)]
mod tests;
