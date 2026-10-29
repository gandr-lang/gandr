//! A run whose independent cuts run at once: each writer the run spawns runs
//! as a job of the caller's fork, over a store of its own, and each read of
//! the writer's handle waits for the writer's answer.
//!
//! The caller schedules the run's IL first
//! ([`gandr_core_sequent::spawn_independent`]). Each cut whose binder focus
//! marked independent is then a perform of [`SPAWN`] of [`CELL`], whose
//! payload is the writer suspended as a thunk. Its binder reads the writer's
//! answer by a perform of [`READ`] of the handle the spawn replied with. No
//! source can claim either operation, so the run offers both to its host.
//! [`evaluate_scheduled_on`] lowers the root and every writer once, then
//! answers both operations inside a scope of the caller's fork:
//!
//! - A spawn copies the thunk into a store of its own, in the process
//!   ([`Store::copy`]), and starts its writer as a job of the scope. The job
//!   runs the thunk's body closed over that store with a host of its own, so a
//!   writer spawns and reads the writers inside it. The reply is the writer's
//!   handle: an integer that names the writer's place in the host's table.
//! - A read waits for the job behind its handle. A job that no worker took runs
//!   on the waiting thread. While another worker runs it, the waiting worker
//!   runs the pool's other jobs. Then the read copies the writer's answer into
//!   the reader's store, and resumes with it.
//!
//! Every other operation, and every migration, goes to the host the caller
//! supplies.
//!
//! # Boundaries
//!
//! - **Code copies as code.** Every run of a schedule shares one arena, so a
//!   thunk, a fixpoint or a closure in a capture or an answer keeps its
//!   command. A writer's function records a site for each closure the root's
//!   function builds, and so lays out any closure its captures hold.
//! - **No lock and no chunk on the way.** A copy goes from store to store, so a
//!   cut takes no lock and writes nothing to the process's chunk store.
//! - **A thunk that does not copy declines its spawn.** A capture holding a
//!   capability does not copy, since a capability's address is its identity.
//!   The run then stops stuck at the spawn. Focus's caller marks no writer that
//!   captures one.
//! - **A read without an answer is declined.** A writer that ends with no
//!   answer, or that panics on another worker, leaves the reader stuck at its
//!   read.
//! - **A writer's own host declines every other operation.** A marked writer
//!   performs nothing: the mark is the claim of focus's caller.
//! - **A handle read twice answers twice.** A continuation resumed twice reads
//!   its handle again, and the host copies the answer it kept.
//! - **Waits stack native frames.** A wait that runs a job on its own thread
//!   runs it on top of its frames, so nested waits stack as deep as the spawn
//!   tree.
//! - **No thread of its own.** The fork is the caller's, so this module starts
//!   no thread.
//!
//! # References
//!
//! - `Pruiksma-2022-back_futures` — background: § 4's configurations, where a
//!   cut allocates an empty cell, its one writer fills it and ends, and a
//!   reader waits until the cell is filled.
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-in-gandr item 1): the concurrent schedule of a cut, its writer
//!   spawned and its cell written once.

use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::convert::Infallible;
use core::mem;

use gandr_core_fork::Fork;
use gandr_core_fork::Scoped;
use gandr_core_fork::Spawn;
use gandr_core_sequent::CELL;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::READ;
use gandr_core_sequent::SPAWN;
use gandr_core_sequent::Store;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_stencils::Fuel;

use crate::lower::Schedule;
use crate::lower::lower_scheduled;
use crate::run::Declined;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::run::closed_on_with_host;
use crate::run::lowered_on_with_host;
use crate::seam::HostHandler;
use crate::seam::HostOutcome;
use crate::seam::HostReply;
use crate::seam::HostRequest;
use crate::seam::HostValues;
use crate::seam::Migrated;
use crate::seam::MigrationRequest;

/// Run `root`, its independent cuts scheduled, on `tier` inside a scope of
/// `fork`: each spawn starts its writer as a job of the scope, and each read
/// waits for the writer's answer.
///
/// # Specification
/// - requires: `root` and every definition it reaches belong to `arena`, as
///   [`evaluate_on_with_host`] requires, scheduled by
///   [`gandr_core_sequent::spawn_independent`] or written so: every perform of
///   [`READ`] of [`CELL`] reads a handle a perform of [`SPAWN`] of [`CELL`]
///   replied with, in the same run.
/// - ensures: the root and each writer's body are lowered once, before the
///   scope starts ([`crate::lower::lower_scheduled`]). The reader runs as
///   [`evaluate_on_with_host`] runs it, with a host that answers each spawn
///   with a handle and each read with a fresh copy of the writer's answer in
///   `store`. A read declines when the writer ended with no answer, and a spawn
///   declines when its thunk does not copy. Each writer runs over the function
///   the schedule lowered for its body and a store of its own, each value its
///   environment binds first laid out on the run's heap as a host's reply is.
///   Its host answers its own spawns and reads and declines every other
///   operation. Every other operation and every migration of the reader goes to
///   `host`. So a run whose writers halt answers as the sequential schedule
///   does.
/// - panics: a panic of a writer that ran on this thread, or of the reader; a
///   writer's panic on another worker where the scope ends.
/// - executable: none — the answer is observed by running the schedule.
///
/// # Errors
/// As [`evaluate_on_with_host`].
///
/// # Adequacy
/// - hypothesis: L2 — a writer over a capture, read after the reader asks the
///   caller's host, nested writers read before their reader's own spawn, a
///   writer over an opaque constant, a writer whose capture is a function, and
///   a recursive writer whose captures hold its own fixpoint answer on each
///   tier what their sequential schedule answers, on the serial fork. A reply
///   copied from the wrong store, a handle naming another writer, or another
///   operation not passed on changes an answer. L3 — a writer stuck at an
///   operation leaves the reader stuck at its read. The driver's pool, at one
///   thread and at four, is `gandr-surface-dispatcher`'s witness.
/// - witness: `tests::cut::a_read_answers_what_its_writer_halts_with`
/// - witness: `tests::cut::nested_writers_answer_as_their_sequential_schedule`
/// - witness: `tests::cut::a_writer_with_no_answer_leaves_its_read_stuck`
/// - witness: `tests::cut::a_writer_over_an_opaque_constant_answers_as_its_sequential_schedule`
/// - witness: `tests::cut::a_writer_over_a_captured_function_answers_as_its_sequential_schedule`
/// - witness: `tests::cut::a_recursive_writer_capturing_its_own_fixpoint_answers_2954`
///
/// [`evaluate_on_with_host`]: crate::evaluate_on_with_host
#[inline]
pub fn evaluate_scheduled_on<Forking, Host>(
    fork: &Forking,
    tier: Tier,
    (arena, definitions, root): (&CommandArena, &Definitions, CommandId),
    (fuel, store): (Fuel, &mut Store),
    host: &mut Host,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Forking: Fork,
    Host: HostHandler + Send,
    Host::Abort: Send,
{
    let schedule = lower_scheduled(arena, definitions, root)?;
    fork.scope(Reading {
        program: Program {
            tier,
            arena,
            definitions,
            schedule: &schedule,
            fuel,
        },
        store,
        host,
    })
}

/// What every run of a schedule reads besides its store: the tier, the
/// program, its code, and the fuel.
#[derive(Clone, Copy, Debug)]
struct Program<'scope>
{
    /// The tier every run takes.
    tier: Tier,
    /// The IL every run's command belongs to.
    arena: &'scope CommandArena,
    /// The definitions every run unfolds.
    definitions: &'scope Definitions,
    /// The reader's function and each writer's, lowered once for the run.
    schedule: &'scope Schedule,
    /// The jumps each run may take.
    fuel: Fuel,
}

/// The reader: the scheduled root, run over the caller's store with the
/// caller's host behind the cell's.
#[derive(Debug)]
struct Reading<'scope, 'run, Host>
{
    /// The program the root belongs to.
    program: Program<'scope>,
    /// The caller's store.
    store: &'run mut Store,
    /// The caller's host.
    host: &'run mut Host,
}

impl<'scope, Host> Scoped<'scope> for Reading<'scope, '_, Host>
where
    Host: HostHandler,
{
    type Output = Result<HostOutcome<Host::Abort>, Declined>;

    /// Run the root with a host that starts its writers on `spawner`.
    ///
    /// # Specification
    /// trivial.
    fn run<Spawner>(
        self,
        spawner: &Spawner,
    ) -> Self::Output
    where
        Spawner: Spawn<'scope>,
    {
        let Self {
            program,
            store,
            host,
        } = self;
        let mut scheduling = Scheduling {
            program,
            spawner,
            cells: Vec::new(),
            host,
        };
        lowered_on_with_host(
            program.tier,
            &program.schedule.reader,
            (program.arena, program.definitions),
            (program.fuel, RunInputs::new(store)),
            &mut scheduling,
        )
    }
}

/// A writer a spawn started: the thunk's body, closed over a store of its
/// own.
#[derive(Debug)]
struct Writing<'scope>
{
    /// The program the body belongs to.
    program: Program<'scope>,
    /// The thunk's body, binding one covariable.
    body: CommandId,
    /// The thunk's environment in `store`.
    environment: Environment,
    /// The writer's own store, which keeps its answer.
    store: Store,
}

/// How a writer ended: its store, and the answer it halted with there.
#[derive(Debug)]
struct Written
{
    /// The writer's store.
    store: Store,
    /// The value the writer halted with, if it halted.
    answer: Option<HeapValueId>,
}

impl<'scope> Scoped<'scope> for Writing<'scope>
{
    type Output = Written;

    /// Run the writer, its own spawns started on `spawner`.
    ///
    /// # Specification
    /// trivial.
    fn run<Spawner>(
        self,
        spawner: &Spawner,
    ) -> Written
    where
        Spawner: Spawn<'scope>,
    {
        let Self {
            program,
            body,
            environment,
            mut store,
        } = self;
        let answer = closed(program, spawner, (body, environment), &mut store);
        Written { store, answer }
    }
}

/// Run a writer's `body` over `store` with a host that starts its spawns on
/// `spawner`, and answer the value it halts with there; none for a body the
/// schedule did not lower.
///
/// # Specification
/// trivial.
fn closed<'scope, Spawner>(
    program: Program<'scope>,
    spawner: &Spawner,
    (body, environment): (CommandId, Environment),
    store: &mut Store,
) -> Option<HeapValueId>
where
    Spawner: Spawn<'scope>,
{
    let lowered = program.schedule.writers.get(&body)?;
    let mut declining = Declining;
    let mut scheduling = Scheduling {
        program,
        spawner,
        cells: Vec::new(),
        host: &mut declining,
    };
    match closed_on_with_host(
        program.tier,
        lowered,
        (program.arena, program.definitions),
        environment,
        (program.fuel, RunInputs::new(store)),
        &mut scheduling,
    ) {
        Ok(HostOutcome::Completed(Outcome::Halted(answer))) => Some(answer),
        Ok(HostOutcome::Completed(Outcome::Stuck(_))) | Err(_) => None,
        Ok(HostOutcome::Aborted(never)) => match never {},
    }
}

/// A host that declines every operation: a writer's host behind the cell's.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct Declining;

impl HostHandler for Declining
{
    type Abort = Infallible;

    /// Decline the operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        HostReply::Decline
    }
}

/// A writer's place in its host's table, which its handle names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Place(usize);

impl Place
{
    /// The handle naming this place: a non-negative integer literal.
    ///
    /// # Specification
    /// trivial.
    fn handle(self) -> Option<HeapValue>
    {
        Magnitude::from_decimal_text(self.0.to_string()).map(|magnitude| {
            HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
                Sign::NonNegative,
                magnitude,
            )))
        })
    }

    /// The place `handle` names, if it is a handle.
    ///
    /// # Specification
    /// trivial.
    fn named(handle: Option<&HeapValue>) -> Option<Self>
    {
        let Some(&HeapValue::Literal(Literal::Integer(ref integer))) = handle
        else {
            return None;
        };
        if integer.sign() != Sign::NonNegative {
            return None;
        }
        integer.magnitude().as_ref().parse().ok().map(Self)
    }
}

/// One writer of a host's table.
enum Cell<'scope, Spawner>
where
    Spawner: Spawn<'scope>,
{
    /// The writer runs as a job of the scope.
    Started(Spawner::Spawned<Writing<'scope>>),
    /// The writer's job ended, and its store keeps its answer.
    Ended(Written),
    /// The writer ended with no answer.
    Unanswered,
}

/// The host of one run of a schedule: it answers the cell's spawns and reads,
/// and gives every other operation to `host`.
struct Scheduling<'scope, 'run, Spawner, Host>
where
    Spawner: Spawn<'scope>,
{
    /// The program every writer belongs to.
    program: Program<'scope>,
    /// The scope's spawner.
    spawner: &'run Spawner,
    /// The writers this run spawned, by place.
    cells: Vec<Cell<'scope, Spawner>>,
    /// The host of every other operation.
    host: &'run mut Host,
}

impl<'scope, Spawner, Host> Scheduling<'scope, '_, Spawner, Host>
where
    Spawner: Spawn<'scope>,
    Host: HostHandler,
{
    /// Start the writer `payload` suspends, and resume with its handle; a
    /// thunk that does not copy declines.
    ///
    /// # Specification
    /// trivial.
    fn spawn(
        &mut self,
        payload: HeapValueId,
        values: &mut HostValues<'_>,
    ) -> HostReply<Host::Abort>
    {
        let mut store = Store::new();
        let Ok(copied) = store.copy(values.store(), payload)
        else {
            return HostReply::Decline;
        };
        let Some(&HeapValue::Thunk { body, environment }) = store.value(copied)
        else {
            return HostReply::Decline;
        };
        let Some(handle) = Place(self.cells.len()).handle()
        else {
            return HostReply::Decline;
        };
        let Ok(handle) = values.allocate(handle)
        else {
            return HostReply::Decline;
        };
        self.cells.push(Cell::Started(self.spawner.spawn(Writing {
            program: self.program,
            body,
            environment,
            store,
        })));
        HostReply::Resume(handle)
    }

    /// Wait for the writer `payload` names, and resume with its answer
    /// copied into the reader's store.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        payload: HeapValueId,
        values: &mut HostValues<'_>,
    ) -> HostReply<Host::Abort>
    {
        let Some(Place(place)) = Place::named(values.value(payload))
        else {
            return HostReply::Decline;
        };
        let Some(cell) = self.cells.get_mut(place)
        else {
            return HostReply::Decline;
        };
        let written = match mem::replace(cell, Cell::Unanswered) {
            Cell::Started(started) => self.spawner.wait(started).ok(),
            Cell::Ended(written) => Some(written),
            Cell::Unanswered => None,
        };
        let Some(written) = written
        else {
            return HostReply::Decline;
        };
        let answer = written
            .answer
            .and_then(|answer| values.store().copy(&written.store, answer).ok());
        *cell = Cell::Ended(written);
        answer.map_or(HostReply::Decline, HostReply::Resume)
    }
}

impl<'scope, Spawner, Host> HostHandler for Scheduling<'scope, '_, Spawner, Host>
where
    Spawner: Spawn<'scope>,
    Host: HostHandler,
{
    type Abort = Host::Abort;

    /// Answer the cell's spawns and reads, and any other operation as the
    /// caller's host decides.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        if request.signature.name().as_ref() != CELL {
            return self.host.handle(request, values);
        }
        match request.operation.as_ref() {
            SPAWN => self.spawn(request.payload, values),
            READ => self.read(request.payload, values),
            _ => self.host.handle(request, values),
        }
    }

    /// Decide a migration as the caller's host decides it.
    ///
    /// # Specification
    /// trivial.
    fn migrate(
        &mut self,
        request: MigrationRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> Migrated
    {
        self.host.migrate(request, values)
    }
}
