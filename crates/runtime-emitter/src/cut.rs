//! A cut forked: its writer and its reader run as the two halves of one join
//! on the fork the caller hands over, and the reader reads the writer's answer
//! through a host's reply.
//!
//! The writer is the cut's producer, a command binding one covariable, run
//! closed over the values its own store binds ([`evaluate_closed_on`]). The
//! reader is the rest of the program, run with a host
//! ([`evaluate_on_with_host`]). The two meet at the cut's cell. At halt the
//! writer writes its store and its answer into the cell, once. A writer that
//! ends with no answer, or that panics, writes that end instead. A read is a
//! perform of [`READ`] of [`CELL`], which no source can claim, so the reader's
//! run offers it to its host. The host waits until the cell holds its write.
//! Then it crosses the answer into the reader's store through the process's
//! chunk store, as the answer of a migration crosses, and resumes the read
//! with it. The host gives every other operation to the host the caller
//! supplies.
//!
//! # Boundaries
//!
//! - **The writer is the left half.** A fork begins the left half before it
//!   waits for the right half to end, so a reader that waits for its writer
//!   waits for a writer that runs already or has ended. The serial fork runs
//!   the writer to its end first, and the read finds the cell written.
//! - **The answer crosses by content.** Each run's heap belongs to its thread,
//!   so the reply is a fresh copy in the reader's store, and the writer's store
//!   keeps the answer it halted with. A value that does not cross leaves the
//!   read unanswered.
//! - **A read without an answer is declined.** The reader's run then stops
//!   stuck at the read, and the writer's outcome says why.
//! - **No thread of its own.** The fork is the caller's, so this module starts
//!   no thread.
//!
//! # References
//!
//! - `Pruiksma-2022-back_futures` — background: § 4's configurations, where a
//!   cut allocates an empty cell, its one writer fills it and ends, and a
//!   reader waits until the cell is filled; the writer stands left of its
//!   readers.
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-in-gandr item 1): the concurrent schedule of a cut, its cell
//!   written once.

use std::sync::Condvar;
use std::sync::Mutex;
use std::sync::PoisonError;

use gandr_core_fork::Fork;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Environment;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_runtime_stencils::Fuel;

use crate::run::Declined;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::run::evaluate_closed_on;
use crate::run::evaluate_on_with_host;
use crate::seam::HostHandler;
use crate::seam::HostOutcome;
use crate::seam::HostReply;
use crate::seam::HostRequest;
use crate::seam::HostValues;
use crate::seam::Migrated;
use crate::seam::MigrationRequest;

/// The interface whose one operation, [`READ`], reads a cut's cell, named so
/// that no source can claim it: no handler a source writes answers it, so the
/// reader's run offers the read to its host.
pub const CELL: &str = "?cell";

/// The one operation of [`CELL`]: its reply is the writer's answer.
pub const READ: &str = "read";

/// A cut's writer: its producer cut against the covariable the run delivers
/// to, closed over the values `environment` binds in `store`.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Writer<'store>
{
    /// The command, binding one covariable.
    pub body: CommandId,
    /// The values `body` captures, in `store`.
    pub environment: Environment,
    /// The writer's own store, which keeps its answer.
    pub store: &'store mut Store,
}

/// A cut's reader: the root whose run reads the cell, over `store`, every
/// other operation offered to `host`.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Reader<'store, 'host, Host>
{
    /// The command the reader runs.
    pub root: CommandId,
    /// The reader's own store, which the reply is laid out in.
    pub store: &'store mut Store,
    /// The host of every operation but the read.
    pub host: &'host mut Host,
}

/// How each half of a forked cut ended.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Forked<Abort>
{
    /// The writer's outcome, moved into its store.
    pub writer: Result<Outcome, Declined>,
    /// The reader's outcome, moved into its store.
    pub reader: Result<HostOutcome<Abort>, Declined>,
}

/// Run a cut's writer and its reader as the two halves of one join on `fork`,
/// on `tier`, the reader reading the writer's answer through the cell.
///
/// # Specification
/// - requires: `writer.body` and `reader.root` belong to `arena`, and
///   `writer.environment` binds `writer.body`'s captures in `writer.store`, as
///   [`evaluate_closed_on`] requires. Every perform of [`READ`] of [`CELL`] in
///   the reader's run reads this cut's cell, and its reply type is the type of
///   the writer's answer.
/// - ensures: the writer runs as [`evaluate_closed_on`] runs it, its outcome
///   moved into `writer.store`. The reader runs as [`evaluate_on_with_host`]
///   runs it with a host that answers each read: after the writer halts, with a
///   fresh copy of the writer's answer in `reader.store`; after the writer ends
///   otherwise, or when the answer does not cross, with a decline. Every other
///   operation and every migration goes to `reader.host`. So the reader answers
///   as the sequential schedule does: the writer to its end first, then the
///   reader.
/// - panics: a panic of either half, once both have ended.
/// - executable: none — the answer is observed by running both halves.
///
/// # Adequacy
/// - hypothesis: L2 — a writer over a capture and a reader that performs one
///   other operation before its read, joined on the serial fork and on a fork
///   that starts the reader first, answer on each tier what the reader answers
///   with the writer's answer as its reply; a reply crossed from the wrong
///   store, a read answered before the write, or another operation not passed
///   on changes an answer. L3 — a writer stuck at an operation it has no host
///   for leaves the reader stuck at its read, on both forks.
/// - witness: `tests::cut::a_read_answers_what_its_writer_halts_with`
/// - witness: `tests::cut::a_writer_with_no_answer_leaves_its_read_stuck`
#[inline]
pub fn evaluate_cut_on<Forking, Host>(
    fork: &Forking,
    tier: Tier,
    (arena, definitions): (&CommandArena, &Definitions),
    (writer, reader): (Writer<'_>, Reader<'_, '_, Host>),
    fuel: Fuel,
) -> Forked<Host::Abort>
where
    Forking: Fork,
    Host: HostHandler + Send,
    Host::Abort: Send,
{
    let cell = Cell::new();
    let cell = &cell;
    let Writer {
        body,
        environment,
        store,
    } = writer;
    let Reader {
        root,
        store: read_into,
        host,
    } = reader;
    let (written, read) = fork.join(
        move || {
            let unanswered = Unanswered(cell);
            let outcome = evaluate_closed_on(
                tier,
                (arena, definitions),
                (body, environment),
                (fuel, RunInputs::new(store)),
            );
            if let Ok(Outcome::Halted(answer)) = outcome {
                cell.write(Written::Answer(store, answer));
            }
            drop(unanswered);
            outcome
        },
        move || {
            let mut reading = Reading { cell, host };
            evaluate_on_with_host(
                tier,
                (arena, definitions, root),
                (fuel, RunInputs::new(read_into)),
                &mut reading,
            )
        },
    );
    Forked {
        writer: written,
        reader: read,
    }
}

/// What the writer wrote into the cell.
#[derive(Clone, Copy, Debug)]
enum Written<'store>
{
    /// The writer halted with this value of its store.
    Answer(&'store Store, HeapValueId),
    /// The writer ended with no answer, or panicked.
    Unanswered,
}

/// A cut's cell: empty until its writer writes it, once.
#[derive(Debug)]
struct Cell<'store>
{
    /// The write, once there is one.
    written: Mutex<Option<Written<'store>>>,
    /// Signalled when the write lands.
    filled: Condvar,
}

impl<'store> Cell<'store>
{
    /// An empty cell.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            written: Mutex::new(None),
            filled: Condvar::new(),
        }
    }

    /// Write `written` into the cell unless it holds a write already, and wake
    /// every reader waiting for it.
    ///
    /// # Specification
    /// trivial.
    fn write(
        &self,
        written: Written<'store>,
    )
    {
        let mut slot = self.written.lock().unwrap_or_else(PoisonError::into_inner);
        if slot.is_none() {
            *slot = Some(written);
        }
        drop(slot);
        self.filled.notify_all();
    }

    /// Wait until the cell holds its write, then answer the read with the
    /// writer's answer crossed into `values`' store, or decline it.
    ///
    /// # Specification
    /// trivial.
    fn read<Abort>(
        &self,
        values: &mut HostValues<'_>,
    ) -> HostReply<Abort>
    {
        let slot = self.written.lock().unwrap_or_else(PoisonError::into_inner);
        let slot = self
            .filled
            .wait_while(slot, |slot| slot.is_none())
            .unwrap_or_else(PoisonError::into_inner);
        match *slot {
            Some(Written::Answer(store, answer)) => values
                .cross_from(store, answer)
                .map_or(HostReply::Decline, HostReply::Resume),
            Some(Written::Unanswered) | None => HostReply::Decline,
        }
    }
}

/// Writes the cell's end with no answer when dropped, so a writer that ends
/// with no answer, or panics, still writes its cell.
#[repr(transparent)]
#[derive(Debug)]
struct Unanswered<'cell, 'store>(&'cell Cell<'store>);

impl Drop for Unanswered<'_, '_>
{
    /// Write the end with no answer unless the writer wrote its answer.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.0.write(Written::Unanswered);
    }
}

/// The reader's host: it answers the cell's read and gives every other
/// operation to the caller's host.
#[derive(Debug)]
struct Reading<'cell, 'store, 'host, Host>
{
    /// The cut's cell.
    cell: &'cell Cell<'store>,
    /// The caller's host.
    host: &'host mut Host,
}

impl<Host> HostHandler for Reading<'_, '_, '_, Host>
where
    Host: HostHandler,
{
    type Abort = Host::Abort;

    /// Answer a read of the cell from the cell, and any other operation as the
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
        if request.signature.name().as_ref() == CELL && request.operation.as_ref() == READ {
            self.cell.read(values)
        }
        else {
            self.host.handle(request, values)
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
