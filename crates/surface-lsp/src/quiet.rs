//! Quiet publication: red only where the user is not typing.
//!
//! # A diagnostic of the form under the caret waits
//!
//! The form an author is writing is unended until its terminator arrives, and
//! each keystroke rechecks it and refuses it again. Publishing that refusal at
//! every keystroke paints the line red while the author is still writing it.
//! The server keeps the caret's proxy — the end of the text the last ranged
//! change inserted, since the protocol never sends the caret itself — and
//! finds the innermost form holding it ([`caret_form`]) in the tree the
//! session's judgement of the revision already parsed, so the hold costs no
//! second parse on the way to the publication. A diagnostic whose range
//! touches that form is *held*: it is not published with the rest. Every other
//! diagnostic publishes at once, as before, so a refusal the edit causes
//! elsewhere still shows on the keystroke that causes it. A goal is never
//! held: a hole's goal is what the author is reading while writing the hole.
//!
//! A held diagnostic publishes when the next change leaves the form — the
//! hold is recomputed for each change from the caret it carries — when the
//! change that closes the form arrives, since a caret just past a written `;`
//! or `}` is in no form the tile closes, or after the document goes
//! [`QUIET`] without a change: one deadline per document, re-armed by each
//! change, after which the full set publishes at the version it was checked
//! at. A held diagnostic waits only while changes keep arriving in its form,
//! and never longer than the interval after the last of them; it is never
//! dropped. The `gandr.diagnostics.quiet` setting, pushed with the `gandr`
//! section as `diagnostics.verbosity` is, names the interval in seconds;
//! `0` holds nothing, which is the publication before the hold.
//!
//! The hold is a property of publication alone. The session checks every
//! revision whole, as before; `gandr check`, the REPL and the terminal face
//! read the dispatcher's entries and see nothing different. A complete but
//! wrong token inside the form under the caret shows after the interval or at
//! the form's terminator: that is the trade. The hold is recomputed from each
//! change's caret and keeps no memory of what it released, so typing again in
//! a form whose refusal the interval published holds that refusal again.
//!
//! - Precedent: rust-analyzer splits its own diagnostics by the work they need
//!   — syntax diagnostics from the parse and semantic ones from analysis,
//!   computed as separate tasks and kept apart until published — so what the
//!   parse can say is never kept waiting by what analysis has yet to compute.
//!   The same split is drawn here by place rather than by pass: what the author
//!   is writing waits, what the edit broke elsewhere does not.
//! - Alternatives: debouncing the whole publication, which delays a real error
//!   elsewhere as long as one under the caret; holding the form under the caret
//!   until a terminator alone, which leaves a form the author abandons unended
//!   red-free for good; a client-side caret notification, which needs an
//!   extension Helix and Zed cannot run.
//! - Reversal: a scenario in which the last change's end is not where the
//!   author is typing — a multi-cursor edit, a paste ending elsewhere — and the
//!   hold misplaces measurably, moves the caret to a client notification with
//!   the case recorded. A measured flicker — refusals published at the interval
//!   and held again as typing resumes in their form — keeps a released refusal
//!   published until its form changes shape.
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
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::time::Instant;

use anodized::spec;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::Severity;
use crate::rpc::Classified;
use crate::rpc::Last;
use crate::rpc::classify;
use crate::rpc::ends;
use crate::server::Logged;
use crate::transport::TransportFault;
use crate::transport::read_frame;

/// How long a document goes without a change before the diagnostics held for
/// the form under its caret publish, when the client names no other interval.
pub const QUIET: Duration = Duration::from_millis(1500);

quenchant_shape::reason_enum! {
    /// Why no form holds a caret.
    pub mod formless {
        /// The reason no form is under the caret.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// Every form ends before the caret or begins at or after it, or
            /// ends there with its last tile written.
            Between,
            /// No caret was asked about: the last change named no range, or
            /// the hold is off.
            Uncareted,
            /// The revision has no tree: the built-in grammar did not build,
            /// or the revision's parse did not commit.
            Unparsed,
        }
    }
}

/// The innermost form of `tree` holding the caret at `at`: the smallest form
/// that begins before `at` and either ends after it or is unended and reaches
/// it.
///
/// A form whose last tile is written ends at that tile: a caret just past a
/// `;` or a `}` has left the form the tile closes. A form the parser ended
/// with a repair — grout where a term is missing, a close the source never
/// wrote — is still being written, as is a top-level form that is not a meld,
/// so a caret at its end, or in the layout after it, is inside it: the space
/// typed between two words of a declaration does not leave it.
///
/// # Specification
/// - requires: `at` is a byte offset of `tree`'s source.
/// - ensures: the span of the shortest form — a meld of `tree`, or a top-level
///   form that is not one — whose start is before `at` and whose end is after
///   `at`, or, for an unended form, whose end or the whitespace after it
///   reaches `at`; a meld is unended when the last leaf of its last children
///   that are neither space nor documentation is grout or a minted close, and a
///   top-level form that is not a meld always is. [`formless::Absent::Between`]
///   when no form is.
/// - provides: the form the quiet publication holds diagnostics for.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the tree's nodes; a form's last leaf is read only
///   for a meld whose span already holds the caret's start.
///
/// # Adequacy
/// - hypothesis: L3 — a caret at the end of a declaration missing its `;` is
///   inside it, as is one after a space typed there; one past the `;` is in no
///   form, and one inside an operand of a finished declaration is in the
///   operand's form; a caret before a lone word at the top level is in no form,
///   and one after it is in the word.
/// - witness: `quiet::tests::the_caret_is_held_by_the_form_it_is_writing`
#[spec(ensures: |ret| match ret {
    Maybe::Present(span) => span.start() < at,
    Maybe::Absent(_) => true,
})]
pub fn caret_form(
    tree: &SyntaxTree<'_>,
    at: ByteOffset,
) -> Maybe<ByteSpan, formless::Absent>
{
    let source = tree.source();
    let text: &str = source.as_ref();
    // Whether the whitespace after a form ending at `span` reaches the caret.
    let reaches = |span: ByteSpan| {
        let after = text.get(usize::from(span.end()) ..).unwrap_or_default();
        let layout = after.len().saturating_sub(after.trim_start().len());
        usize::from(at) <= usize::from(span.end()).saturating_add(layout)
    };
    let melds = tree.positions().filter_map(|position| {
        let node = tree.node(position)?;
        let span = node.span();
        (matches!(node.label(), NodeLabel::Meld(_))
            && span.start() < at
            && (at < span.end() || (ends_in_repair(tree, position).0 && reaches(span))))
        .then_some(span)
    });
    let lone = tree.forms().iter().filter_map(|&position| {
        let node = tree.node(position)?;
        let span = node.span();
        (!matches!(node.label(), NodeLabel::Meld(_))
            && span.start() < at
            && (at < span.end() || reaches(span)))
        .then_some(span)
    });
    melds
        .chain(lone)
        .min_by_key(|span| usize::from(span.end()).saturating_sub(usize::from(span.start())))
        .map_or(Maybe::Absent(formless::Absent::Between), Maybe::Present)
}

/// Whether a form's last leaf is a repair.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EndsInRepair(bool);

/// Whether the last leaf under `position`, read through each last child that
/// is neither space nor documentation, is grout or a minted close.
///
/// # Specification
/// trivial.
fn ends_in_repair(
    tree: &SyntaxTree<'_>,
    position: NodeIndex,
) -> EndsInRepair
{
    let mut at = position;
    loop {
        let Some(node) = tree.node(at)
        else {
            return EndsInRepair(false);
        };
        match node.label() {
            NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => return EndsInRepair(true),
            NodeLabel::Tile(_) | NodeLabel::Space => return EndsInRepair(false),
            NodeLabel::Wald | NodeLabel::Meld(_) | NodeLabel::Doc => {
                let last = tree.children(at).filter(|&child| {
                    tree.node(child).is_some_and(|child| {
                        !matches!(child.label(), NodeLabel::Space | NodeLabel::Doc)
                    })
                });
                match last.last() {
                    Some(child) => at = child,
                    None => return EndsInRepair(false),
                }
            },
        }
    }
}

/// Whether a publication withheld any diagnostic.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Holding(pub bool);

/// The diagnostics of `checked` that publish now, with the form under the
/// caret at `form`: every one whose range does not touch the form, and every
/// goal.
///
/// # Specification
/// - requires: `form` and every range of `checked` are ranges of one text.
/// - ensures: `checked` in order, less each diagnostic other than a goal whose
///   range meets `form`'s, both ends included; all of `checked` when no form is
///   under the caret. [`Holding`] says whether any was left out.
/// - provides: the hold, computed afresh for each publication.
/// - fails: never.
/// - panics: none.
/// - intension: one comparison of two positions per diagnostic.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal inside the form under the caret is held, one
///   two declarations below is not, a goal inside the form is not, and with no
///   form every diagnostic publishes.
/// - witness: `tests::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
/// - witness: `quiet::tests::a_diagnostic_touching_the_form_is_held_and_one_apart_from_it_published`
#[spec(ensures: |ret| ret.0.len() <= checked.len() && ret.1.0 == (ret.0.len() < checked.len()))]
#[must_use]
pub fn publishable<Reason>(
    checked: &[Diagnostic],
    form: &Maybe<Range, Reason>,
) -> (Vec<Diagnostic>, Holding)
{
    let Maybe::Present(form) = *form
    else {
        return (checked.to_vec(), Holding(false));
    };
    let published: Vec<Diagnostic> = checked
        .iter()
        .filter(|diagnostic| {
            diagnostic.severity == Severity::INFORMATION
                || diagnostic.range.start > form.end
                || diagnostic.range.end < form.start
        })
        .cloned()
        .collect();
    let holding = Holding(published.len() < checked.len());
    (published, holding)
}

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

/// What a paced loop meets next.
#[derive(Debug)]
pub enum Met<'later>
{
    /// A message the client sent, and the messages it sent after that one
    /// which were read before the loop came to it, in order.
    Frame
    {
        /// The message, as its envelope classifies it.
        message: Classified,
        /// The messages already read after it.
        later: &'later [Classified],
    },
    /// A document whose deadline passed.
    Quiet(DocumentUri),
    /// Files a watch beside the loop saw change on disk, sorted.
    Changed(Vec<PathBuf>),
    /// Files another connection's editor changed in the copy it holds,
    /// sorted.
    Edited(Vec<PathBuf>),
    /// Another connection kept a checked fill of a document this connection
    /// holds a copy of.
    Proposed,
    /// The client's stream closed at a frame boundary.
    Closed,
}

/// What the reading thread, or a watch beside it, hands the loop.
#[derive(Debug)]
enum Read
{
    /// A message, classified.
    Message(Classified),
    /// Files changed on disk.
    Changed(Vec<PathBuf>),
    /// Files another connection's editor changed.
    Edited(Vec<PathBuf>),
    /// A checked fill of a document the loop's connection holds was kept.
    Proposed,
    /// The stream closed at a frame boundary.
    Closed,
    /// The stream failed.
    Fault(TransportFault),
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
    proposed: &mut Proposed,
) -> Option<End>
{
    match read {
        Read::Message(message) => {
            queued.push_back(message);
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
        Read::Closed => Some(End::Closed),
        Read::Fault(fault) => Some(End::Fault(fault)),
    }
}

/// Whether a checked fill was kept since the loop last said so.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Proposed(bool);

/// Where a paced loop takes what it meets: its reader's messages and a
/// watch's changes.
#[derive(Debug)]
pub struct Inbox
{
    /// The sending end, for the reader and each watch.
    sending: mpsc::Sender<Read>,
    /// The receiving end, the loop's.
    receiving: mpsc::Receiver<Read>,
}

impl Default for Inbox
{
    /// An empty inbox.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        let (sending, receiving) = mpsc::channel();
        Self { sending, receiving }
    }
}

impl Inbox
{
    /// A handle a watch hands this inbox's loop the files it saw change by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn changes(&self) -> Changes
    {
        Changes(self.sending.clone())
    }
}

/// A handle a watch, or another connection, hands a paced loop the files it
/// saw change by.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Changes(mpsc::Sender<Read>);

impl Changes
{
    /// Hand the loop `paths`, changed on disk; nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn hand(
        &self,
        paths: Vec<PathBuf>,
    )
    {
        let _sent = self.0.send(Read::Changed(paths));
    }

    /// Hand the loop `paths`, changed in another connection's editor;
    /// nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edited(
        &self,
        paths: Vec<PathBuf>,
    )
    {
        let _sent = self.0.send(Read::Edited(paths));
    }

    /// Tell the loop another connection kept a checked fill of a document its
    /// connection holds; nothing once the loop ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn proposed(&self)
    {
        let _sent = self.0.send(Read::Proposed);
    }
}

/// Serve `input` through `visit`: each message read, each deadline passed,
/// each change a watch hands `inbox` and the end of the stream, in the order
/// they come, until `visit` breaks.
///
/// # Specification
/// - requires: nothing of the stream.
/// - ensures: frames are read as they arrive, on a scoped thread that
///   classifies each once and stops after `exit`, at the stream's end or at its
///   first fault; each message is handed to `visit` as [`Met::Frame`], in
///   order, with every message already read after it; the files a watch hands
///   `inbox` through [`Inbox::changes`] are gathered, sorted and without
///   repeats, and handed to `visit` as [`Met::Changed`] before the next
///   message, the files another connection's editor changed as [`Met::Edited`]
///   after them, and the fills another connection kept as one [`Met::Proposed`]
///   after those; while nothing waits, each document whose deadline in the
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
///   read while the one before was handled is handed over with it, and a
///   watch's changes reach the loop gathered.
/// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
/// - witness: `tests::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `tests::session::a_stream_closed_without_exit_ends_abruptly`
/// - witness: `quiet::tests::a_message_read_while_another_is_handled_comes_with_it`
/// - witness: `quiet::tests::nothing_past_exit_is_read`
/// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
#[inline]
pub fn paced<Input, Visit, Ended>(
    input: &mut Input,
    inbox: Inbox,
    mut visit: Visit,
) -> Result<Ended, TransportFault>
where
    Input: BufRead + Send,
    Visit: FnMut(Met<'_>, &mut Deadlines) -> Result<ControlFlow<Ended>, TransportFault>,
{
    let Inbox {
        sending: read,
        receiving: frames,
    } = inbox;
    std::thread::scope(|scope| {
        let _reader = scope.spawn(move || {
            loop {
                let (frame, last) = match read_frame(input) {
                    Ok(Maybe::Present(body)) => {
                        let message = classify(&body);
                        let Last(last) = ends(&message);
                        (Read::Message(message), last)
                    },
                    Ok(Maybe::Absent(_)) => (Read::Closed, true),
                    Err(fault) => (Read::Fault(fault), true),
                };
                let ended = matches!(frame, Read::Message(_)) && last;
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
        let mut end: Option<End> = None;
        loop {
            if queued.is_empty()
                && changed.is_empty()
                && edited.is_empty()
                && proposed == Proposed(false)
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
                                &mut proposed,
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
            while end.is_none()
                && let Ok(frame) = frames.try_recv()
            {
                end = queue(
                    frame,
                    &mut queued,
                    (&mut changed, &mut edited),
                    &mut proposed,
                );
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
mod tests
{
    use std::io;

    use gandr_surface_parser::parse;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Holding;
    use super::caret_form;
    use super::formless;
    use super::publishable;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::Severity;
    use crate::recheck::grammar;

    /// The range from `start` to `end` on line zero.
    ///
    /// # Specification
    /// trivial.
    fn columns(
        start: impl Into<Character>,
        end: impl Into<Character>,
    ) -> Range
    {
        let line = Line::from(0_u32);
        Range {
            start: Position {
                line,
                character: start.into(),
            },
            end: Position {
                line,
                character: end.into(),
            },
        }
    }

    /// An error marking `range`, saying `message`.
    ///
    /// # Specification
    /// trivial.
    fn error(
        range: Range,
        message: impl Into<String>,
    ) -> Diagnostic
    {
        Diagnostic {
            range,
            severity: Severity::ERROR,
            code: None,
            source: "gandr",
            message: message.into(),
            related_information: Vec::new(),
        }
    }

    #[test]
    fn a_diagnostic_touching_the_form_is_held_and_one_apart_from_it_published()
    {
        let form: Maybe<Range, ()> = Maybe::Present(columns(10_u32, 20_u32));
        let messages = |published: &[Diagnostic]| -> Vec<String> {
            published
                .iter()
                .map(|diagnostic| diagnostic.message.clone())
                .collect()
        };
        let checked = [
            error(columns(0_u32, 5_u32), "before"),
            error(columns(5_u32, 10_u32), "touching its start"),
            error(columns(12_u32, 14_u32), "inside"),
            error(columns(20_u32, 25_u32), "touching its end"),
            error(columns(21_u32, 25_u32), "after"),
        ];
        let (published, holding) = publishable(&checked, &form);
        assert_eq!(messages(&published), ["before", "after"]);
        assert_eq!(holding, Holding(true));
        let apart = [
            error(columns(0_u32, 5_u32), "before"),
            error(columns(21_u32, 25_u32), "after"),
        ];
        let (published, holding) = publishable(&apart, &form);
        assert_eq!(messages(&published), ["before", "after"]);
        assert_eq!(holding, Holding(false), "nothing held, nothing withheld");
    }

    #[test]
    fn the_caret_is_held_by_the_form_it_is_writing()
    {
        let grammar = grammar().expect("the built-in grammar builds");
        // The bytes of the form holding the caret at `at` in `text`, or why
        // none does.
        let held = |text: &'static str, at: usize| {
            let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
            match caret_form(parsed.tree(), ByteOffset::from(at)) {
                Maybe::Present(span) => Maybe::Present(
                    text.get(usize::from(span.start()) .. usize::from(span.end()))
                        .unwrap_or_default(),
                ),
                Maybe::Absent(absent) => Maybe::Absent(absent),
            }
        };
        let text = "def a = 1 ;\ndef b = ";
        assert_eq!(
            held(text, text.len()),
            Maybe::Present("def b ="),
            "a caret at the end of a declaration missing its value is inside it"
        );
        assert_eq!(
            held("def b", 3),
            Maybe::Present("def b"),
            "and of one missing all but its keyword"
        );
        let spaced = "def b = f \n";
        assert_eq!(
            held(spaced, spaced.len()),
            Maybe::Present("def b = f"),
            "the layout after an unended declaration is still inside it"
        );
        assert_eq!(
            held(text, 11),
            Maybe::Absent(formless::Absent::Between),
            "a caret just past a `;` has left the declaration the `;` ends"
        );
        assert_eq!(
            held(text, 12),
            Maybe::Absent(formless::Absent::Between),
            "as has one at the start of the next line"
        );
        let Maybe::Present(inner) = held(text, 9)
        else {
            panic!("a caret inside a finished declaration is in one of its forms");
        };
        assert!(
            "def a = 1 ;".contains(inner) && inner.contains('1'),
            "the form holding a caret inside the value is the value's or the declaration's: {inner:?}"
        );
        let lone = "def a = 1 ;\nx";
        assert_eq!(
            held(lone, 12),
            Maybe::Absent(formless::Absent::Between),
            "a caret before a lone word has not entered it"
        );
        assert_eq!(
            held(lone, 13),
            Maybe::Present("x"),
            "one after it is writing it"
        );
    }

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
                | super::Met::Proposed => core::ops::ControlFlow::Continue(()),
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
                | super::Met::Proposed => core::ops::ControlFlow::Continue(()),
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
}
