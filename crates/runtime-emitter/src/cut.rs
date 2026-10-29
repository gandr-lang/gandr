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
//! [`evaluate_scheduled_on`] answers them inside a scope of the caller's fork:
//!
//! - A spawn crosses the thunk into a store of its own through the process's
//!   chunk store, and starts its writer as a job of the scope. The job runs the
//!   thunk's body closed over that store with a host of its own, so a writer
//!   spawns and reads the writers inside it. The reply is the writer's handle:
//!   an integer that names the writer's place in the host's table.
//! - A read waits for the job behind its handle. A job that no worker took runs
//!   on the waiting thread. While another worker runs it, the waiting worker
//!   runs the pool's other jobs. Then the read crosses the writer's answer into
//!   the reader's store, and resumes with it.
//!
//! Every other operation, and every migration, goes to the host the caller
//! supplies.
//!
//! # Boundaries
//!
//! - **A thunk that does not cross runs at its read.** Its writer then runs on
//!   the reader's thread, over the reader's store, as a run nested in the
//!   read's reply.
//! - **The answer crosses by content.** Each writer's store is its own, so the
//!   reply is a fresh copy in the reader's store. A value that does not cross
//!   leaves the read unanswered.
//! - **A read without an answer is declined.** A writer that ends with no
//!   answer, or that panics on another worker, leaves the reader stuck at its
//!   read.
//! - **A writer's own host declines every other operation.** A marked writer
//!   performs nothing: the mark is the claim of focus's caller.
//! - **A handle read twice answers twice.** A continuation resumed twice reads
//!   its handle again, and the host crosses the answer it kept.
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

use crate::run::Declined;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::run::evaluate_closed_on_with_host;
use crate::run::evaluate_on_with_host;
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
/// - ensures: the reader runs as [`evaluate_on_with_host`] runs it, with a host
///   that answers each spawn with a handle and each read with a fresh copy of
///   the writer's answer in `store`, or a decline when the writer ended with no
///   answer. Each writer runs as [`evaluate_closed_on`] runs it, over a store
///   of its own, with a host that answers its own spawns and reads and declines
///   every other operation. Every other operation and every migration of the
///   reader goes to `host`. So a run whose writers halt answers as the
///   sequential schedule does.
/// - panics: a panic of a writer that ran on this thread, or of the reader; a
///   writer's panic on another worker where the scope ends.
/// - executable: none — the answer is observed by running the schedule.
///
/// # Errors
/// As [`evaluate_on_with_host`].
///
/// # Adequacy
/// - hypothesis: L2 — a writer over a capture, read after the reader asks the
///   caller's host, and nested writers read before their reader's own spawn,
///   answer on each tier what their sequential schedule answers, on the serial
///   fork; a reply crossed from the wrong store, a handle naming another
///   writer, or another operation not passed on changes an answer. L3 — a
///   writer stuck at an operation leaves the reader stuck at its read, and a
///   writer whose thunk does not cross runs at its read. The driver's pool, at
///   one thread and at four, is `gandr-surface-dispatcher`'s witness.
/// - witness: `tests::cut::a_read_answers_what_its_writer_halts_with`
/// - witness: `tests::cut::nested_writers_answer_as_their_sequential_schedule`
/// - witness: `tests::cut::a_writer_with_no_answer_leaves_its_read_stuck`
/// - witness: `tests::cut::a_writer_that_does_not_cross_runs_at_its_read`
///
/// [`evaluate_closed_on`]: crate::evaluate_closed_on
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
    fork.scope(Reading {
        program: Program {
            tier,
            arena,
            definitions,
            fuel,
        },
        root,
        store,
        host,
    })
}

/// What every run of a schedule reads besides its command and its store: the
/// tier, the program, and the fuel.
#[derive(Clone, Copy, Debug)]
struct Program<'scope>
{
    /// The tier every run takes.
    tier: Tier,
    /// The IL every run's command belongs to.
    arena: &'scope CommandArena,
    /// The definitions every run unfolds.
    definitions: &'scope Definitions,
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
    /// The scheduled root.
    root: CommandId,
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
            root,
            store,
            host,
        } = self;
        let mut scheduling = Scheduling {
            program,
            spawner,
            cells: Vec::new(),
            host,
        };
        evaluate_on_with_host(
            program.tier,
            (program.arena, program.definitions, root),
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
/// `spawner`, and answer the value it halts with there.
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
    let mut declining = Declining;
    let mut scheduling = Scheduling {
        program,
        spawner,
        cells: Vec::new(),
        host: &mut declining,
    };
    match evaluate_closed_on_with_host(
        program.tier,
        (program.arena, program.definitions),
        (body, environment),
        (program.fuel, RunInputs::new(store)),
        &mut scheduling,
    ) {
        Ok(HostOutcome::Completed(Outcome::Halted(answer))) => Some(answer),
        Ok(HostOutcome::Completed(Outcome::Stuck(_))) | Err(_) => None,
        Ok(HostOutcome::Aborted(never)) => match never {},
    }
}

/// A writer's host behind the cell's: it declines every operation.
#[derive(Clone, Copy, Debug)]
struct Declining;

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
    /// The writer's thunk did not cross, so it runs at its read, over the
    /// reader's store.
    Suspended
    {
        /// The thunk's body.
        body: CommandId,
        /// The thunk's environment in the reader's store.
        environment: Environment,
    },
    /// The writer's job ended, and its store keeps its answer.
    Ended(Written),
    /// The writer ran at its read, and halted with this value of the reader's
    /// store.
    Here(HeapValueId),
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
    /// Start the writer `payload` suspends, and resume with its handle.
    ///
    /// # Specification
    /// trivial.
    fn spawn(
        &mut self,
        payload: HeapValueId,
        values: &mut HostValues<'_>,
    ) -> HostReply<Host::Abort>
    {
        let Some(&HeapValue::Thunk { body, environment }) = values.value(payload)
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
        let mut store = Store::new();
        let crossed = values
            .cross_to(payload, &mut store)
            .ok()
            .and_then(|crossed| {
                let Some(&HeapValue::Thunk { body, environment }) = store.value(crossed)
                else {
                    return None;
                };
                Some((body, environment))
            });
        let cell = match crossed {
            Some((body, environment)) => Cell::Started(self.spawner.spawn(Writing {
                program: self.program,
                body,
                environment,
                store,
            })),
            None => Cell::Suspended { body, environment },
        };
        self.cells.push(cell);
        HostReply::Resume(handle)
    }

    /// Wait for the writer `payload` names, and resume with its answer
    /// crossed into the reader's store.
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
        let (kept, answer) = match mem::replace(cell, Cell::Unanswered) {
            Cell::Started(started) => {
                self.spawner
                    .wait(started)
                    .map_or((Cell::Unanswered, None), |written| {
                        let answer = written
                            .answer
                            .and_then(|answer| values.cross_from(&written.store, answer).ok());
                        (Cell::Ended(written), answer)
                    })
            },
            Cell::Ended(written) => {
                let answer = written
                    .answer
                    .and_then(|answer| values.cross_from(&written.store, answer).ok());
                (Cell::Ended(written), answer)
            },
            Cell::Suspended { body, environment } => {
                let answer = closed(
                    self.program,
                    self.spawner,
                    (body, environment),
                    values.store(),
                );
                (answer.map_or(Cell::Unanswered, Cell::Here), answer)
            },
            Cell::Here(answer) => (Cell::Here(answer), Some(answer)),
            Cell::Unanswered => (Cell::Unanswered, None),
        };
        *cell = kept;
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
