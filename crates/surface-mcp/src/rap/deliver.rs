//! The deliveries of the toolset: each callback that the toolset owes to a
//! runtime, tried until the runtime takes it or the policy gives it up.
//!
//! A row is a pending call or a subscription. A row has one delivery in
//! flight at most, and the deliveries of other rows go beside it on the
//! toolset's own threads. A newer state of a subscription replaces the state
//! that waits for its turn, so a runtime receives the latest state of each row
//! and the table holds two states of a row at most.
//!
//! # Boundaries
//!
//! A `2xx` takes a delivery. A `5xx`, a timeout and a connection that fails
//! try it again after the first wait of the [`Policy`], doubled after each
//! attempt up to its longest wait, until the retries of the policy are spent.
//! Then the toolset drops the delivery, counts the drop and tells the log. A
//! subscription stays, and its next state starts again from the first
//! attempt. A result stays in the store, and the toolset tries it again when a
//! later delivery to the same callback URL succeeds. Any other status refuses
//! the delivery, and the toolset tries it no more.
//!
//! Each body is the routing of its row, then the text of its state, then a
//! closing brace. The toolset encodes the text of a state once, and every
//! delivery of that state shares the bytes.

use alloc::collections::BTreeMap;
use alloc::collections::BinaryHeap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cmp::Reverse;
use core::fmt;
use core::time::Duration;
use std::io;
use std::io::IoSlice;
use std::io::Read as _;
use std::io::Write as _;
use std::net::TcpStream;
use std::net::ToSocketAddrs as _;
use std::sync::Condvar;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Instant;

use super::HEAD_LIMIT;
use super::HEADERS;
use crate::face::lock;

/// How long one attempt waits on a callback, to connect, to send and to hear
/// the status: five seconds. A runtime acknowledges a delivery at once. An
/// attempt that waits longer fails, and the policy tries it again.
const CALLBACK_WAIT: Duration = Duration::from_secs(5);

/// When the toolset tries a failed delivery again, and how often: a recipe
/// policy of the hub, which the `[deliveries]` table of its configuration
/// names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Policy
{
    /// The wait before the first retry. Each later wait doubles it.
    pub first: Duration,
    /// The longest wait between two attempts.
    pub longest: Duration,
    /// The attempts after the first.
    pub retries: Retries,
}

/// A count of retries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Retries(pub u32);

impl Default for Policy
{
    /// A first wait of 250 ms, doubled up to 30 s, over 8 retries: about 62
    /// seconds from the first attempt to the last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            first: Duration::from_millis(250),
            longest: Duration::from_secs(30),
            retries: Retries(8),
        }
    }
}

impl Policy
{
    /// The wait after the attempt that failed as the `tried`th, from one.
    ///
    /// # Specification
    /// trivial.
    fn wait(
        &self,
        tried: Retries,
    ) -> Duration
    {
        let doublings = tried.0.saturating_sub(1).min(31);
        self.first
            .saturating_mul(1_u32.checked_shl(doublings).unwrap_or(u32::MAX))
            .min(self.longest)
    }
}

/// A row that a delivery answers, by its `group_id` and its identifier.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Row
{
    /// A pending call: its `group_id` and its `id`.
    Call(String, String),
    /// A subscription: its `group_id` and its `tool_call_id`.
    Subscription(String, String),
}

impl fmt::Display for Row
{
    /// The row as the log names it.
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
            Self::Call(ref group_id, ref id) => write!(f, "the call {id} of {group_id}"),
            Self::Subscription(ref group_id, ref tool_call_id) => {
                write!(f, "the subscription {tool_call_id} of {group_id}")
            },
        }
    }
}

/// One state of a row to deliver: where it goes, and its body.
pub struct Post
{
    /// The callback URL.
    pub callback_url: Arc<str>,
    /// The bearer that the caller sent, sent back as `Authorization: Bearer`.
    pub token: Option<Arc<str>>,
    /// The `Idempotency-Key` header: `<tool_call_id>@<version>` for an event
    /// and the `id` for a result.
    pub key: String,
    /// The body up to its text: the routing of the row, as JSON fields.
    pub head: String,
    /// The text of the state, encoded once as a JSON string, which every
    /// delivery of the state shares.
    pub text: Arc<str>,
}

/// The status that a callback answered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Status(pub u16);

/// The drops of a toolset so far.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Drops(pub u64);

/// How the deliveries of a row ended.
#[derive(Debug)]
pub enum Fate
{
    /// The runtime took the delivery.
    Taken,
    /// The runtime refused the delivery with a status that no retry changes.
    Refused(Status),
    /// Every attempt failed: the last error, and the drops of the toolset
    /// with this one.
    Spent(io::Error, Drops),
}

impl fmt::Display for Fate
{
    /// The fate as the log tells it.
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
            Self::Taken => f.write_str("taken"),
            Self::Refused(Status(status)) => write!(f, "refused with {status}"),
            Self::Spent(ref error, Drops(drops)) => write!(
                f,
                "dropped after its last attempt failed ({error}); drops so far: {drops}"
            ),
        }
    }
}

/// A state owed to a row, and the attempts that failed for it.
struct Owed
{
    /// The state.
    post: Post,
    /// The attempts that failed.
    tried: Retries,
}

/// The deliveries of one row.
#[derive(Default)]
struct Lane
{
    /// The state that waits for its turn or for its next attempt.
    owed: Option<Owed>,
    /// Whether a worker holds the row's delivery now.
    flying: bool,
    /// The newest state, which waits behind the delivery in flight.
    next: Option<Post>,
    /// The ticket of the row's entry in the due heap. An entry with another
    /// ticket is stale.
    ticket: u64,
}

/// What the deliveries hold under their lock.
#[derive(Default)]
struct Table
{
    /// The rows that owe a delivery.
    lanes: BTreeMap<Row, Lane>,
    /// When each row's next attempt is due, earliest first, by ticket.
    due: BinaryHeap<Reverse<(Instant, u64, Row)>>,
    /// The results whose retries are spent, by callback URL.
    parked: BTreeMap<Arc<str>, Vec<(Row, Post)>>,
    /// The last ticket given.
    tickets: u64,
    /// Whether the toolset stopped.
    closed: bool,
    /// The deliveries dropped so far.
    dropped: u64,
}

impl Table
{
    /// Owe `post` to `row`, due at `at` when the row owes nothing yet.
    ///
    /// # Specification
    /// trivial.
    fn owe(
        &mut self,
        row: Row,
        post: Post,
        at: Instant,
    )
    {
        let lane = self.lanes.entry(row.clone()).or_default();
        if lane.flying {
            lane.next = Some(post);
            return;
        }
        if let Some(ref mut owed) = lane.owed {
            // The newer state keeps the turn and the attempts of the older one.
            owed.post = post;
            return;
        }
        lane.owed = Some(Owed {
            post,
            tried: Retries(0),
        });
        self.tickets = self.tickets.saturating_add(1);
        lane.ticket = self.tickets;
        self.due.push(Reverse((at, self.tickets, row)));
    }

    /// Owe `owed` to `row` again, due at `at`.
    ///
    /// # Specification
    /// trivial.
    fn again(
        &mut self,
        row: &Row,
        owed: Owed,
        at: Instant,
    )
    {
        if let Some(lane) = self.lanes.get_mut(row) {
            lane.owed = Some(owed);
            self.tickets = self.tickets.saturating_add(1);
            lane.ticket = self.tickets;
            self.due.push(Reverse((at, self.tickets, row.clone())));
        }
    }

    /// End the flight of `row`: owe its newest state when one waits, and
    /// forget the row otherwise.
    ///
    /// # Specification
    /// trivial.
    fn landed(
        &mut self,
        row: &Row,
        at: Instant,
    )
    {
        let next = self.lanes.get_mut(row).and_then(|lane| {
            lane.flying = false;
            lane.next.take()
        });
        match next {
            Some(post) => self.again(
                row,
                Owed {
                    post,
                    tried: Retries(0),
                },
                at,
            ),
            None => drop(self.lanes.remove(row)),
        }
    }
}

/// The deliveries the toolset owes, and the policy that retries them.
pub struct Deliveries
{
    /// The table.
    table: Mutex<Table>,
    /// Woken when a delivery is owed or the toolset stops.
    ready: Condvar,
    /// When to retry, and how often.
    policy: Policy,
}

impl Deliveries
{
    /// No delivery yet, retried as `policy` states.
    ///
    /// # Specification
    /// trivial.
    pub fn new(policy: Policy) -> Self
    {
        Self {
            table: Mutex::new(Table::default()),
            ready: Condvar::new(),
            policy,
        }
    }

    /// Owe `post` to `row`.
    ///
    /// # Specification
    /// trivial.
    pub fn owe(
        &self,
        row: Row,
        post: Post,
    )
    {
        lock(&self.table).owe(row, post, Instant::now());
        self.ready.notify_one();
    }

    /// Stop: each worker returns once its delivery in flight ends.
    ///
    /// # Specification
    /// trivial.
    pub fn close(&self)
    {
        lock(&self.table).closed = true;
        self.ready.notify_all();
    }

    /// Deliver what is owed until the toolset stops, telling `told` how the
    /// deliveries of each row ended.
    ///
    /// # Specification
    /// trivial.
    pub fn run<Told>(
        &self,
        mut told: Told,
    ) where
        Told: FnMut(&Row, Fate),
    {
        let mut exchange = Exchange::default();
        while let Some((row, owed)) = self.take() {
            let sent = post(&owed.post, &mut exchange);
            if let Some(fate) = self.settle(&row, owed, sent) {
                told(&row, fate);
            }
        }
    }

    /// The next delivery due, waiting for it, or none once the toolset
    /// stopped.
    ///
    /// # Specification
    /// trivial.
    fn take(&self) -> Option<(Row, Owed)>
    {
        let mut table = lock(&self.table);
        loop {
            if table.closed {
                return None;
            }
            let now = Instant::now();
            let next = table.due.peek().map(|&Reverse((at, ..))| at);
            match next {
                Some(at) if at <= now => {
                    let Some(Reverse((_at, ticket, row))) = table.due.pop()
                    else {
                        continue;
                    };
                    let owed = table
                        .lanes
                        .get_mut(&row)
                        .filter(|lane| lane.ticket == ticket && !lane.flying)
                        .and_then(|lane| {
                            lane.flying = true;
                            lane.owed.take()
                        });
                    if let Some(owed) = owed {
                        return Some((row, owed));
                    }
                },
                Some(at) => {
                    table = self
                        .ready
                        .wait_timeout(table, at.saturating_duration_since(now))
                        .map_or_else(|poisoned| poisoned.into_inner().0, |(table, _)| table);
                },
                None => {
                    table = self
                        .ready
                        .wait(table)
                        .unwrap_or_else(PoisonError::into_inner);
                },
            }
        }
    }

    /// Record how the attempt of `owed` for `row` went: schedule a retry, or
    /// end the row's flight with its fate.
    ///
    /// # Specification
    /// trivial.
    fn settle(
        &self,
        row: &Row,
        mut owed: Owed,
        sent: io::Result<Status>,
    ) -> Option<Fate>
    {
        let now = Instant::now();
        let mut table = lock(&self.table);
        let error = match sent {
            Ok(Status(200 ..= 299)) => {
                table.landed(row, now);
                let parked = table.parked.remove(&owed.post.callback_url);
                let woken = parked.is_some();
                for (parked, post) in parked.into_iter().flatten() {
                    table.owe(parked, post, now);
                }
                drop(table);
                if woken {
                    self.ready.notify_all();
                }
                return Some(Fate::Taken);
            },
            Ok(Status(500 ..= 599)) => io::Error::other("the callback answered a server error"),
            Ok(status) => {
                drop(table.lanes.remove(row));
                drop(table);
                return Some(Fate::Refused(status));
            },
            Err(error) => error,
        };
        if owed.tried < self.policy.retries {
            owed.tried = Retries(owed.tried.0.saturating_add(1));
            let at = now.checked_add(self.policy.wait(owed.tried)).unwrap_or(now);
            if let Some(lane) = table.lanes.get_mut(row) {
                lane.flying = false;
                if let Some(newer) = lane.next.take() {
                    owed.post = newer;
                }
            }
            table.again(row, owed, at);
            drop(table);
            self.ready.notify_one();
            return None;
        }
        table.dropped = table.dropped.saturating_add(1);
        let drops = Drops(table.dropped);
        if matches!(*row, Row::Call(..)) {
            table
                .parked
                .entry(Arc::clone(&owed.post.callback_url))
                .or_default()
                .push((row.clone(), owed.post));
        }
        table.landed(row, now);
        drop(table);
        Some(Fate::Spent(error, drops))
    }
}

/// The bytes of one exchange with a callback, kept to be used again.
#[repr(transparent)]
#[derive(Default)]
struct Exchange(Vec<u8>);

/// Post `post` to its callback URL and read the status, the head of the
/// request and the answer written in `exchange`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The error resolving, connecting, writing or reading.
fn post(
    post: &Post,
    exchange: &mut Exchange,
) -> io::Result<Status>
{
    use core::fmt::Write as _;

    let rest = post
        .callback_url
        .strip_prefix("http://")
        .ok_or_else(|| io::Error::other("the callback URL is not an `http` URL"))?;
    let (authority, path) = rest
        .find('/')
        .map_or((rest, "/"), |slash| rest.split_at(slash));
    let mut addresses = if authority.ends_with(']') || !authority.contains(':') {
        (
            authority.trim_start_matches('[').trim_end_matches(']'),
            80_u16,
        )
            .to_socket_addrs()?
    }
    else {
        authority.to_socket_addrs()?
    };
    let address = addresses
        .next()
        .ok_or_else(|| io::Error::other("the callback URL names no address"))?;
    let mut stream = TcpStream::connect_timeout(&address, CALLBACK_WAIT)?;
    stream.set_read_timeout(Some(CALLBACK_WAIT))?;
    stream.set_write_timeout(Some(CALLBACK_WAIT))?;
    stream.set_nodelay(true)?;
    let length = post
        .head
        .len()
        .saturating_add(post.text.len())
        .saturating_add(1);
    let mut head = String::new();
    write!(
        head,
        "POST {path} HTTP/1.1\r\nhost: {authority}\r\ncontent-type: application/json\r\ncontent-length: {length}\r\nidempotency-key: {}\r\n",
        post.key
    )
    .map_err(io::Error::other)?;
    if let Some(ref token) = post.token {
        write!(head, "authorization: Bearer {token}\r\n").map_err(io::Error::other)?;
    }
    head.push_str("connection: close\r\n\r\n");
    let mut slices = [
        IoSlice::new(head.as_bytes()),
        IoSlice::new(post.head.as_bytes()),
        IoSlice::new(post.text.as_bytes()),
        IoSlice::new(b"}"),
    ];
    let mut unsent = &mut slices[..];
    while !unsent.is_empty() {
        let written = stream.write_vectored(unsent)?;
        if written == 0 {
            return Err(io::ErrorKind::WriteZero.into());
        }
        IoSlice::advance_slices(&mut unsent, written);
    }
    exchange.0.clear();
    let mut chunk = [0_u8; 1024];
    loop {
        let read = stream.read(&mut chunk)?;
        if read == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        exchange
            .0
            .extend_from_slice(chunk.get(.. read).unwrap_or_default());
        let mut headers = [httparse::EMPTY_HEADER; HEADERS];
        let mut answer = httparse::Response::new(&mut headers);
        match answer.parse(&exchange.0).map_err(io::Error::other)? {
            httparse::Status::Complete(_head) => {
                return Ok(Status(answer.code.unwrap_or_default()));
            },
            httparse::Status::Partial if exchange.0.len() > HEAD_LIMIT => {
                return Err(io::ErrorKind::InvalidData.into());
            },
            httparse::Status::Partial => {},
        }
    }
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;

    use super::Policy;
    use super::Retries;

    #[test]
    fn a_wait_doubles_up_to_the_longest()
    {
        let policy = Policy::default();
        let waits: alloc::vec::Vec<Duration> = (1 ..= policy.retries.0)
            .map(|tried| policy.wait(Retries(tried)))
            .collect();
        assert_eq!(
            waits,
            [250, 500, 1_000, 2_000, 4_000, 8_000, 16_000, 30_000].map(Duration::from_millis),
            "the default policy waits about 62 seconds over its retries"
        );
    }
}
