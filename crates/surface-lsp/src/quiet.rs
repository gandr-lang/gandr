//! The paced loop of the quiet publication, and the deadline of each document
//! whose publication held a diagnostic. The hold itself is in
//! `gandr-surface-lsp-base`.
//!
//! # A loop reads frames on a thread of its own
//!
//! A deadline expires while no frame arrives, so the loop that serves a
//! connection cannot block in a read. [`paced`] reads frames on a scoped
//! thread as they arrive, classifies each once, and hands them to the loop,
//! which waits for a message or the earliest deadline, whichever comes first.
//! The loop takes every message the thread has read before it handles the
//! first of them, so a request is handled knowing what the client sent after
//! it: a cancellation naming it, or a change of the document it reads. The
//! thread stops after `exit`, as the client sends nothing after it the server
//! reads, and at the end of the stream.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::ops::ControlFlow;
use core::time::Duration;
use std::io::BufRead;
use std::path::PathBuf;
use std::sync::mpsc::RecvTimeoutError;
use std::time::Instant;

use anodized::spec;
use gandr_surface_lsp_base::quiet::Met;
use quenchant_shape::shape::Maybe;

use crate::inbox::Behind;
use crate::inbox::Inbox;
use crate::inbox::Read;
use crate::inbox::Unread;
use crate::protocol::DocumentUri;
use crate::rpc::Classified;
use crate::rpc::Last;
use crate::rpc::classify;
use crate::rpc::ends;
use crate::server::Logged;
use crate::transport::TransportFault;
use crate::transport::read_frame;

/// The deadline of each document whose last publication held a diagnostic.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct Deadlines(BTreeMap<DocumentUri, Instant>);

impl Deadlines
{
    /// Arm or disarm the deadline of each document `log` synchronised: armed
    /// `quiet` after `now` when its publication held a diagnostic, dropped
    /// otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each document a line of `log` names has a deadline exactly
    ///   when its last line held, `quiet` after `now`, or none when no instant
    ///   is that far off; every other deadline is kept.
    /// - provides: the one timer per document, re-armed by each change.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held publication arms the deadline and a change
    ///   that holds nothing disarms it.
    /// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
    #[spec(ensures: |_| log.last().is_none_or(|last| {
        !last.holding().0 || now.checked_add(quiet).is_none() || self.0.contains_key(last.uri())
    }))]
    #[inline]
    pub fn note(
        &mut self,
        log: &[Logged],
        quiet: Duration,
        now: Instant,
    )
    {
        for logged in log {
            match (logged.holding().0, now.checked_add(quiet)) {
                (true, Some(deadline)) => {
                    let _armed = self.0.insert(logged.uri().clone(), deadline);
                },
                (true, None) | (false, _) => {
                    let _disarmed = self.0.remove(logged.uri());
                },
            }
        }
    }

    /// Disarm the deadline of each document a line of `log`, settled after its
    /// synchronisation, names that holds nothing back now.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no document whose line holds nothing has a deadline; every
    ///   other deadline is kept as it was, never re-armed.
    /// - provides: the deadline of a document whose admission's correction
    ///   replaced what its publication held back.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Deadlines::note`].
    /// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
    #[spec(ensures: log.iter().all(|logged| logged.holding().0 || !self.0.contains_key(logged.uri())))]
    #[inline]
    pub fn settled(
        &mut self,
        log: &[Logged],
    )
    {
        for logged in log {
            if !logged.holding().0 {
                let _disarmed = self.0.remove(logged.uri());
            }
        }
    }

    /// The earliest deadline, when one is armed.
    ///
    /// # Specification
    /// trivial.
    fn next(&self) -> Option<Instant>
    {
        self.0.values().min().copied()
    }

    /// Take the documents whose deadline is at or before `now`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the documents whose deadline is at or before `now`, each
    ///   disarmed; every later deadline is kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Deadlines::note`].
    /// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
    #[spec(ensures: |ret| ret.iter().all(|uri| !self.0.contains_key(uri)))]
    fn due(
        &mut self,
        now: Instant,
    ) -> Vec<DocumentUri>
    {
        let due: Vec<DocumentUri> = self
            .0
            .iter()
            .filter(|&(_, &deadline)| deadline <= now)
            .map(|(uri, _)| uri.clone())
            .collect();
        for uri in &due {
            let _disarmed = self.0.remove(uri);
        }
        due
    }
}

/// How the stream a loop reads ended.
#[derive(Debug)]
enum End
{
    /// It closed at a frame boundary.
    Closed,
    /// It failed.
    Fault(TransportFault),
}

/// Queue what the reading thread, a watch or another connection handed over,
/// and say how the stream ended when it did.
///
/// # Specification
/// trivial.
fn queue(
    read: Read,
    queued: &mut VecDeque<Classified>,
    (changed, edited): (&mut BTreeSet<PathBuf>, &mut BTreeSet<PathBuf>),
    (proposed, admitted, traced, behind): (&mut Proposed, &mut Woken, &mut Traced, &mut Behind),
) -> Option<End>
{
    match read {
        Read::Message(message, past) => {
            queued.push_back(message);
            *behind = past;
            None
        },
        Read::Changed(paths) => {
            changed.extend(paths);
            None
        },
        Read::Edited(paths) => {
            edited.extend(paths);
            None
        },
        Read::Proposed => {
            *proposed = Proposed(true);
            None
        },
        Read::Admitted => {
            *admitted = Woken(true);
            None
        },
        Read::Traced => {
            *traced = Traced(true);
            None
        },
        Read::Closed => Some(End::Closed),
        Read::Fault(fault) => Some(End::Fault(fault)),
    }
}

/// Whether a checked fill was kept since the loop last said so.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Proposed(bool);

/// Whether an admission ended since the loop last said so.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Woken(bool);

/// Whether the first view of the trace layer subscribed since the loop last
/// said so.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Traced(bool);

/// Serve `input` through `visit`: each message read, each deadline passed,
/// each change a watch hands `inbox` and the end of the stream, in the order
/// they come, until `visit` breaks.
///
/// # Specification
/// - requires: nothing of the stream.
/// - ensures: frames are read as they arrive, on a scoped thread that
///   classifies each once and stops after `exit`, at the stream's end or at its
///   first fault; each message is handed to `visit` as [`Met::Frame`], in
///   order, with every message already read after it; while the input holds
///   bytes past the last message read, the loop waits for the frames those
///   bytes start, so the frames of one write are handed over together; the
///   files a watch hands `inbox` through [`Inbox::changes`] are gathered,
///   sorted and without repeats, and handed to `visit` as [`Met::Changed`]
///   before the next message, the files another connection's editor changed as
///   [`Met::Edited`] after them, and the fills another connection kept as one
///   [`Met::Proposed`] after those, and the admissions its connection started
///   that ended, through
///   [`Changes::admitted`](crate::inbox::Changes::admitted), as one
///   [`Met::Admitted`] after that, and the subscription of the first view of
///   the trace layer, through
///   [`Changes::traced`](crate::inbox::Changes::traced), as one [`Met::Traced`]
///   after that; while nothing waits, each document whose deadline in the
///   [`Deadlines`] `visit` arms passes is handed to `visit` as [`Met::Quiet`],
///   disarmed; a stream closed at a frame boundary, or ended by `exit`, is
///   [`Met::Closed`] once every message before it was handed over, whether or
///   not a watch still holds a handle. The first break `visit` returns is
///   returned.
/// - provides: the loop of [`crate::serve`] and of each hub connection, the
///   later messages a request is withdrawn by, and the hub's watch's way in.
/// - fails: the first [`TransportFault`] of the stream, once every message
///   before it was handed over, and the first `visit` returns.
/// - panics: none.
/// - executable: none — the stream is opaque, and what `visit` writes is its
///   own.
///
/// # Errors
/// [`TransportFault`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — every served editor session runs here; L3 — a held
///   diagnostic publishes after the interval with no frame sent, a session ends
///   at `exit` and at a closed stream, nothing past `exit` is read, a message
///   read while the one before was handled is handed over with it, a write
///   whose second part comes a moment after its first is handed over whole, and
///   a watch's changes reach the loop gathered.
/// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
/// - witness: `tests::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `tests::session::a_stream_closed_without_exit_ends_abruptly`
/// - witness: `quiet::tests::a_message_read_while_another_is_handled_comes_with_it`
/// - witness: `quiet::tests::a_write_read_in_two_parts_is_handed_over_whole_5124`
/// - witness: `quiet::tests::nothing_past_exit_is_read`
/// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the reader thread blocks on the client's frames while the session handles the last one"
    )
)]
#[inline]
pub fn paced<Input, Visit, Ended>(
    input: &mut Input,
    inbox: Inbox,
    mut visit: Visit,
) -> Result<Ended, TransportFault>
where
    Input: BufRead + Unread + Send,
    Visit: FnMut(Met<'_>, &mut Deadlines) -> Result<ControlFlow<Ended>, TransportFault>,
{
    let (read, frames) = inbox.ends();
    std::thread::scope(|scope| {
        let _reader = scope.spawn(move || {
            loop {
                let (frame, last) = match read_frame(input) {
                    Ok(Maybe::Present(body)) => {
                        let message = classify(&body);
                        let Last(last) = ends(&message);
                        (Read::Message(message, input.unread()), last)
                    },
                    Ok(Maybe::Absent(_)) => (Read::Closed, true),
                    Err(fault) => (Read::Fault(fault), true),
                };
                let ended = matches!(frame, Read::Message(..)) && last;
                if read.send(frame).is_err() || last {
                    if ended {
                        // A watch's handle keeps the channel open, so the
                        // stream's end is said rather than left to the
                        // channel's.
                        let _sent = read.send(Read::Closed);
                    }
                    break;
                }
            }
        });
        let mut deadlines = Deadlines::default();
        let mut queued: VecDeque<Classified> = VecDeque::new();
        let mut changed: BTreeSet<PathBuf> = BTreeSet::new();
        let mut edited: BTreeSet<PathBuf> = BTreeSet::new();
        let mut proposed = Proposed::default();
        let mut admitted = Woken::default();
        let mut traced = Traced::default();
        let mut behind = Behind::default();
        let mut end: Option<End> = None;
        loop {
            if queued.is_empty()
                && changed.is_empty()
                && edited.is_empty()
                && proposed == Proposed(false)
                && admitted == Woken(false)
                && traced == Traced(false)
                && end.is_none()
            {
                loop {
                    let received = deadlines.next().map_or_else(
                        || {
                            frames
                                .recv()
                                .map_err(|_gone| RecvTimeoutError::Disconnected)
                        },
                        |deadline| {
                            frames.recv_timeout(deadline.saturating_duration_since(Instant::now()))
                        },
                    );
                    match received {
                        Ok(frame) => {
                            end = queue(
                                frame,
                                &mut queued,
                                (&mut changed, &mut edited),
                                (&mut proposed, &mut admitted, &mut traced, &mut behind),
                            );
                            break;
                        },
                        Err(RecvTimeoutError::Disconnected) => {
                            end = Some(End::Closed);
                            break;
                        },
                        Err(RecvTimeoutError::Timeout) => {
                            for uri in deadlines.due(Instant::now()) {
                                if let ControlFlow::Break(ended) =
                                    visit(Met::Quiet(uri), &mut deadlines)?
                                {
                                    return Ok(ended);
                                }
                            }
                        },
                    }
                }
            }
            // What a watch or an admission hands over after the stream's end
            // is read too, so an admission that ended is settled before the
            // frames still queued.
            while let Ok(frame) = frames.try_recv() {
                if let Some(ended) = queue(
                    frame,
                    &mut queued,
                    (&mut changed, &mut edited),
                    (&mut proposed, &mut admitted, &mut traced, &mut behind),
                ) {
                    let _first = end.get_or_insert(ended);
                }
            }
            // A message read with bytes past it waits for the frames those
            // bytes start, so what the client wrote at once is handed over
            // whole.
            while behind == Behind(true) && end.is_none() {
                end = frames.recv().map_or(Some(End::Closed), |frame| {
                    queue(
                        frame,
                        &mut queued,
                        (&mut changed, &mut edited),
                        (&mut proposed, &mut admitted, &mut traced, &mut behind),
                    )
                });
            }
            if !changed.is_empty() {
                let paths: Vec<PathBuf> = core::mem::take(&mut changed).into_iter().collect();
                if let ControlFlow::Break(ended) = visit(Met::Changed(paths), &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if !edited.is_empty() {
                let paths: Vec<PathBuf> = core::mem::take(&mut edited).into_iter().collect();
                if let ControlFlow::Break(ended) = visit(Met::Edited(paths), &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if proposed == Proposed(true) {
                proposed = Proposed(false);
                if let ControlFlow::Break(ended) = visit(Met::Proposed, &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if admitted == Woken(true) {
                admitted = Woken(false);
                if let ControlFlow::Break(ended) = visit(Met::Admitted, &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if traced == Traced(true) {
                traced = Traced(false);
                if let ControlFlow::Break(ended) = visit(Met::Traced, &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if let Some(message) = queued.pop_front() {
                let met = Met::Frame {
                    message,
                    later: queued.make_contiguous(),
                };
                if let ControlFlow::Break(ended) = visit(met, &mut deadlines)? {
                    return Ok(ended);
                }
                continue;
            }
            if let Some(End::Fault(fault)) = end.take() {
                return Err(fault);
            }
            end = Some(End::Closed);
            if let ControlFlow::Break(ended) = visit(Met::Closed, &mut deadlines)? {
                return Ok(ended);
            }
        }
    })
}

#[cfg(test)]
pub mod tests
{
    use std::io;

    /// A message, spelled as JSON text.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Json<'text>(&'text str);

    /// The frames carrying `messages`, one after another.
    ///
    /// # Specification
    /// trivial.
    fn framed(messages: &[Json<'_>]) -> crate::transport::Body
    {
        let mut bytes = Vec::new();
        for &Json(message) in messages {
            crate::transport::write_frame(
                &mut bytes,
                &crate::transport::Body::from(message.as_bytes().to_vec()),
            )
            .expect("a vector takes a frame");
        }
        crate::transport::Body::from(bytes)
    }

    /// A stream's end that says when it is reached.
    #[repr(transparent)]
    struct Ending(std::sync::mpsc::Sender<()>);

    impl std::io::Read for Ending
    {
        /// Say the end is reached, and read nothing.
        ///
        /// # Specification
        /// trivial.
        fn read(
            &mut self,
            _buffer: &mut [u8],
        ) -> std::io::Result<usize>
        {
            let _sent = self.0.send(());
            Ok(0)
        }
    }

    #[test]
    fn nothing_past_exit_is_read()
    {
        let (reached, reaching) = std::sync::mpsc::channel();
        let bytes = framed(&[
            Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            Json(r#"{"jsonrpc":"2.0","method":"exit"}"#),
        ]);
        let mut input = std::io::BufReader::new(std::io::Read::chain(
            io::Cursor::new(bytes.as_ref().to_vec()),
            Ending(reached),
        ));
        let mut seen = 0_usize;
        let ended = super::paced(&mut input, super::Inbox::default(), |met, _deadlines| {
            Ok(match met {
                super::Met::Frame { message, .. } => {
                    seen = seen.saturating_add(1);
                    if crate::rpc::ends(&message).0 {
                        core::ops::ControlFlow::Break("exit")
                    }
                    else {
                        core::ops::ControlFlow::Continue(())
                    }
                },
                super::Met::Quiet(_)
                | super::Met::Changed(_)
                | super::Met::Edited(_)
                | super::Met::Proposed
                | super::Met::Admitted
                | super::Met::Traced => core::ops::ControlFlow::Continue(()),
                super::Met::Closed => core::ops::ControlFlow::Break("closed"),
            })
        })
        .expect("the stream reads");
        assert_eq!((ended, seen), ("exit", 2_usize));
        assert!(
            reaching.try_recv().is_err(),
            "the reader stopped at `exit` and never read on to the stream's end"
        );
    }

    #[test]
    fn a_message_read_while_another_is_handled_comes_with_it()
    {
        let (reached, reaching) = std::sync::mpsc::channel();
        let bytes = framed(&[
            Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            Json(r#"{"jsonrpc":"2.0","id":1,"method":"shutdown"}"#),
            Json(r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":1}}"#),
        ]);
        let mut input = std::io::BufReader::new(std::io::Read::chain(
            io::Cursor::new(bytes.as_ref().to_vec()),
            Ending(reached),
        ));
        let mut handed: Vec<(String, usize)> = Vec::new();
        super::paced(&mut input, super::Inbox::default(), |met, _deadlines| {
            Ok(match met {
                super::Met::Frame { message, later } => {
                    if handed.is_empty() {
                        // Hold the first message until the reader has read
                        // every frame after it.
                        reaching.recv().expect("the reader reaches the end");
                    }
                    let method = match message {
                        Ok(
                            crate::rpc::Incoming::Request { method, .. }
                            | crate::rpc::Incoming::Notification { method, .. },
                        ) => String::from(method.as_ref()),
                        Ok(crate::rpc::Incoming::Response { .. }) | Err(_) => String::new(),
                    };
                    handed.push((method, later.len()));
                    core::ops::ControlFlow::Continue(())
                },
                super::Met::Quiet(_)
                | super::Met::Changed(_)
                | super::Met::Edited(_)
                | super::Met::Proposed
                | super::Met::Admitted
                | super::Met::Traced => core::ops::ControlFlow::Continue(()),
                super::Met::Closed => core::ops::ControlFlow::Break(()),
            })
        })
        .expect("the stream reads");
        assert_eq!(
            handed
                .iter()
                .map(|&(ref method, _)| method.as_str())
                .collect::<Vec<_>>(),
            ["initialized", "shutdown", "$/cancelRequest"],
            "every message is handed over once, in order"
        );
        assert_eq!(
            handed.get(1).map(|&(_, later)| later),
            Some(1_usize),
            "the request comes with the cancellation read while the message before it was handled"
        );
    }

    /// A stream's part that comes a moment after the part before it, as a
    /// pipe hands the rest of one write to a second read.
    struct Pausing
    {
        /// The bytes of the part.
        rest: io::Cursor<Vec<u8>>,
        /// Whether the pause was waited out.
        paused: bool,
    }

    impl std::io::Read for Pausing
    {
        /// Wait out the pause at the first read, then read on.
        ///
        /// # Specification
        /// trivial.
        fn read(
            &mut self,
            buf: &mut [u8],
        ) -> std::io::Result<usize>
        {
            if !self.paused {
                self.paused = true;
                std::thread::sleep(core::time::Duration::from_millis(50));
            }
            self.rest.read(buf)
        }
    }

    /// #5124: a write whose first read holds one frame and the start of the
    /// next is handed over whole, the first message with the second, though
    /// the rest of the write comes a moment later.
    #[test]
    fn a_write_read_in_two_parts_is_handed_over_whole_5124()
    {
        use std::io::Read as _;

        let bytes = framed(&[
            Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            Json(r#"{"jsonrpc":"2.0","id":1,"method":"shutdown"}"#),
        ]);
        let first = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.len();
        let cut = bytes
            .as_ref()
            .windows(4)
            .position(|window| window == b"\r\n\r\n")
            .map(|header| {
                header
                    .saturating_add(4)
                    .saturating_add(first)
                    .saturating_add(8)
            })
            .expect("the first frame has a header");
        let (head, tail) = bytes.as_ref().split_at(cut);
        let mut input = std::io::BufReader::new(io::Cursor::new(head.to_vec()).chain(Pausing {
            rest: io::Cursor::new(tail.to_vec()),
            paused: false,
        }));
        let mut handed: Vec<usize> = Vec::new();
        super::paced(&mut input, super::Inbox::default(), |met, _deadlines| {
            Ok(match met {
                super::Met::Frame { later, .. } => {
                    handed.push(later.len());
                    core::ops::ControlFlow::Continue(())
                },
                super::Met::Quiet(_)
                | super::Met::Changed(_)
                | super::Met::Edited(_)
                | super::Met::Proposed
                | super::Met::Admitted
                | super::Met::Traced => core::ops::ControlFlow::Continue(()),
                super::Met::Closed => core::ops::ControlFlow::Break(()),
            })
        })
        .expect("the stream reads");
        assert_eq!(
            handed,
            [1_usize, 0_usize],
            "the first message comes with the second, whose start was read with it"
        );
    }
}
