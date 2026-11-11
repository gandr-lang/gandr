//! The work ledger of one subscription to the activity: the events that its
//! runtime did not take yet, bounded, and the one state in flight.
//!
//! Each tick of the hub's fold that has events adds them to the pending
//! events of each row. A row keeps [`PENDING`] events at most. It drops the
//! oldest and counts the drop, so a runtime that stalls holds a bounded
//! memory. A row has one state in flight at most. The state carries every
//! pending event, the drops not yet reported and the row of each core. When
//! the runtime takes it, the row lets go of the events and the drops that it
//! carried. A state whose retries are spent carries nothing away, and the
//! next state carries its events again.
//!
//! The text of a state is JSON: `run`, `dropped`, `events` and `rows`. The
//! run is the time at which the toolset started, in milliseconds since the
//! Unix epoch, and each run numbers its events from zero. So the key of a
//! state, its row, its run and the sequence number of its last event, is
//! never the key of another state.
//!
//! # References
//!
//! - `vault:01a1c6b9-f57a-73c2-b24a-a7b1663d22a8` — anchor: §
//!   agent-layer-stream: `subscribe_activity` hears the work ledger as it
//!   moves, and each event is associative.
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-stream: the activity card only appends, keyed by the
//!   sequence number.

use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec::Vec;
use std::io::Write as _;

use gandr_core_fork::activity::Arrival;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Event;
use gandr_core_fork::activity::Row;
use gandr_core_fork::activity::Sequence;
use gandr_core_fork::activity::Task;
use quenchant_shape::shape::Maybe;
use serde::Serialize;
use serde::Serializer;

/// The events one row keeps for its runtime at most: 128 KiB of events.
pub const PENDING: usize = 4096;

/// The bytes that the text of one event takes, as the buffer of a state
/// reserves them. An event with a sequence number and a clock of 12 digits
/// takes 121 B.
const EVENT_TEXT: usize = 128;

/// The bytes that the text of a state takes besides its events and its rows:
/// the four keys, the run, the drops and the braces.
const STATE_TEXT: usize = 80;

/// The run of a toolset: when it started, in milliseconds since the Unix
/// epoch.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Run(pub u64);

/// The row of each core of the last tick, encoded once as a JSON array for
/// every row that follows the activity.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Occupancy(String);

impl Default for Occupancy
{
    /// No core yet: the empty array.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self(String::from("[]"))
    }
}

/// The state that a row has in flight: the sequence number of its last event
/// and the drops it reports.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Flight
{
    /// The sequence number of the last event that the state carries.
    last: Sequence,
    /// The drops that the state reports.
    dropped: u64,
}

/// The work ledger of one row: its pending events, its drops not yet
/// reported, and its state in flight.
///
/// # Specification
/// - provides: [`Ledger::heard`], which adds a tick's events and bounds them;
///   [`Ledger::owed`], the next state when none is in flight; and
///   [`Ledger::taken`] and [`Ledger::spent`], the two ends of a flight.
/// - panics: none.
/// - executable: none — a queue and two counts.
///
/// # Adequacy
/// - hypothesis: L3 — a row that hears one event past its bound keeps the bound
///   and counts one drop; a state carries every pending event and the drops; a
///   take lets go of what the state carried and keeps what came later; a spent
///   state carries its events again.
/// - witness: `rap::activity::tests::a_row_keeps_its_bound_counts_each_drop_and_lets_go_of_what_was_taken`
#[derive(Debug, Default)]
pub struct Ledger
{
    /// The events that no state the runtime took carried, oldest first.
    pending: VecDeque<Event>,
    /// The events dropped since the last state the runtime took.
    dropped: u64,
    /// The state in flight.
    flight: Option<Flight>,
}

impl Ledger
{
    /// Add `events`, a tick's events in the order of their sequence numbers,
    /// to the pending events. Past [`PENDING`], drop the oldest and count
    /// each drop.
    ///
    /// # Specification
    /// trivial.
    pub fn heard(
        &mut self,
        events: &[Event],
    )
    {
        // Only the last `PENDING` events of the tick can stay.
        let kept = events
            .get(events.len().saturating_sub(PENDING) ..)
            .unwrap_or_default();
        let skipped = events.len().saturating_sub(kept.len());
        let overflow = self
            .pending
            .len()
            .saturating_add(kept.len())
            .saturating_sub(PENDING);
        let gone = self
            .pending
            .drain(.. overflow.min(self.pending.len()))
            .count();
        self.dropped = self
            .dropped
            .saturating_add(u64::try_from(gone.saturating_add(skipped)).unwrap_or(u64::MAX));
        self.pending.extend(kept.iter().copied());
    }

    /// The text of the next state and the sequence number of its last event,
    /// when no state is in flight and an event is pending. The state is in
    /// flight from now on. The text goes into one buffer that the pending
    /// events size. An encode error, which a buffer in memory does not give,
    /// owes nothing, and the events stay pending for the next tick.
    ///
    /// # Specification
    /// trivial.
    pub fn owed(
        &mut self,
        run: Run,
        rows: &Occupancy,
    ) -> Option<(Sequence, String)>
    {
        if self.flight.is_some() {
            return None;
        }
        let last = self.pending.back()?.sequence;
        let mut text: Vec<u8> = Vec::with_capacity(
            self.pending
                .len()
                .saturating_mul(EVENT_TEXT)
                .saturating_add(rows.0.len())
                .saturating_add(STATE_TEXT),
        );
        write!(
            text,
            "{{\"run\":{},\"dropped\":{},\"events\":",
            run.0, self.dropped
        )
        .ok()?;
        serde_json::to_writer(&mut text, &Pending(&self.pending)).ok()?;
        text.extend_from_slice(b",\"rows\":");
        text.extend_from_slice(rows.0.as_bytes());
        text.push(b'}');
        let text = String::from_utf8(text).ok()?;
        self.flight = Some(Flight {
            last,
            dropped: self.dropped,
        });
        Some((last, text))
    }

    /// The runtime took the state in flight: let go of the events and the
    /// drops that it carried.
    ///
    /// # Specification
    /// trivial.
    pub fn taken(&mut self)
    {
        let Some(flight) = self.flight.take()
        else {
            return;
        };
        // The pending events are in the order of their sequence numbers.
        let carried = self
            .pending
            .partition_point(|event| event.sequence <= flight.last);
        drop(self.pending.drain(.. carried));
        self.dropped = self.dropped.saturating_sub(flight.dropped);
    }

    /// The state in flight was dropped after its last retry: the next state
    /// carries its events again.
    ///
    /// # Specification
    /// trivial.
    pub const fn spent(&mut self)
    {
        self.flight = None;
    }
}

/// The text of `rows`, the row of each core, as a JSON array. Each row is its
/// busy nanoseconds in each cell of the last two seconds, oldest first, its
/// busy total, the marks its ring dropped and its late events. The rows hold
/// numbers alone, so the encode does not fail. If it fails, the rows are
/// null.
///
/// # Specification
/// trivial.
pub fn rows(rows: &[Row]) -> Occupancy
{
    Occupancy(serde_json::to_string(&Rows(rows)).unwrap_or_else(|_| String::from("null")))
}

/// The activity card of one tick, as a view update of a running job carries
/// it, and the sequence number of its last event: the run, the events of the
/// tick and the row of each core. A runtime keeps the latest card of each
/// view, so a card carries its own tick alone. A tick with no event owes no
/// card, and an encode error, which a buffer in memory does not give, owes
/// none either.
///
/// # Specification
/// trivial.
pub fn card(
    run: Run,
    events: &[Event],
    rows: &Occupancy,
) -> Option<(Sequence, String)>
{
    let last = events.last()?.sequence;
    let mut text: Vec<u8> = Vec::with_capacity(
        events
            .len()
            .saturating_mul(EVENT_TEXT)
            .saturating_add(rows.0.len())
            .saturating_add(STATE_TEXT),
    );
    write!(text, "{{\"run\":{},\"events\":", run.0).ok()?;
    serde_json::to_writer(&mut text, &Ticked(events)).ok()?;
    text.extend_from_slice(b",\"rows\":");
    text.extend_from_slice(rows.0.as_bytes());
    text.push(b'}');
    Some((last, String::from_utf8(text).ok()?))
}

/// The pending events of a row, as the text of a state holds them.
#[repr(transparent)]
struct Pending<'ledger>(&'ledger VecDeque<Event>);

impl Serialize for Pending<'_>
{
    /// Each event, oldest first.
    ///
    /// # Specification
    /// trivial.
    fn serialize<Out>(
        &self,
        serializer: Out,
    ) -> Result<Out::Ok, Out::Error>
    where
        Out: Serializer,
    {
        serializer.collect_seq(self.0.iter().map(Encoded::of))
    }
}

/// The events of one tick, as the card of a view update holds them.
#[repr(transparent)]
struct Ticked<'tick>(&'tick [Event]);

impl Serialize for Ticked<'_>
{
    /// Each event, in the order of its sequence number.
    ///
    /// # Specification
    /// trivial.
    fn serialize<Out>(
        &self,
        serializer: Out,
    ) -> Result<Out::Ok, Out::Error>
    where
        Out: Serializer,
    {
        serializer.collect_seq(self.0.iter().map(Encoded::of))
    }
}

/// The row of each core, as the text of a state holds them.
#[repr(transparent)]
struct Rows<'rows>(&'rows [Row]);

impl Serialize for Rows<'_>
{
    /// The row of each core, in the order of the cores.
    ///
    /// # Specification
    /// trivial.
    fn serialize<Out>(
        &self,
        serializer: Out,
    ) -> Result<Out::Ok, Out::Error>
    where
        Out: Serializer,
    {
        serializer.collect_seq(self.0.iter().map(Occupied))
    }
}

/// One event as the text of a state holds it.
#[derive(Serialize)]
struct Encoded
{
    /// The place of the event in the ledger of the run.
    sequence: u64,
    /// The hub's clock, in nanoseconds.
    clock: u64,
    /// The core that runs the task.
    core: usize,
    /// The world that the task runs in.
    world: u32,
    /// The kind of the task.
    task: &'static str,
    /// The end of the task: `start` or `end`.
    edge: &'static str,
    /// The ordinal of the declaration, or null.
    declaration: Option<u32>,
    /// Whether the event reached the fold late.
    late: bool,
}

impl Encoded
{
    /// `event`, as the text of a state holds it.
    ///
    /// # Specification
    /// trivial.
    fn of(event: &Event) -> Self
    {
        Self {
            sequence: u64::from(event.sequence),
            clock: u64::from(event.clock),
            core: usize::from(event.core),
            world: u32::from(event.world),
            task: match event.task {
                Task::Fork => "fork",
                Task::Replay => "replay",
                Task::Compile => "compile",
                Task::Fetch => "fetch",
            },
            edge: match event.edge {
                Edge::Start => "start",
                Edge::End => "end",
            },
            declaration: match event.declaration.declaration() {
                Maybe::Present(declaration) => Some(u32::from(declaration)),
                Maybe::Absent(_) => None,
            },
            late: event.arrival == Arrival::Late,
        }
    }
}

/// The row of one core, as the text of a state holds it.
#[repr(transparent)]
struct Occupied<'row>(&'row Row);

impl Serialize for Occupied<'_>
{
    /// The row's cells, its total, its drops and its late events.
    ///
    /// # Specification
    /// trivial.
    fn serialize<Out>(
        &self,
        serializer: Out,
    ) -> Result<Out::Ok, Out::Error>
    where
        Out: Serializer,
    {
        use serde::ser::SerializeStruct as _;

        let mut row = serializer.serialize_struct("Row", 4)?;
        row.serialize_field("cells", &Cells(self.0))?;
        row.serialize_field("busy", &u64::from(self.0.total()))?;
        row.serialize_field("dropped", &u64::from(self.0.dropped()))?;
        row.serialize_field("late", &u64::from(self.0.late()))?;
        row.end()
    }
}

/// The cells of one row, as busy nanoseconds, oldest first.
#[repr(transparent)]
struct Cells<'row>(&'row Row);

impl Serialize for Cells<'_>
{
    /// The busy time of each cell.
    ///
    /// # Specification
    /// trivial.
    fn serialize<Out>(
        &self,
        serializer: Out,
    ) -> Result<Out::Ok, Out::Error>
    where
        Out: Serializer,
    {
        serializer.collect_seq(self.0.cells().map(u64::from))
    }
}

#[cfg(test)]
mod tests;
