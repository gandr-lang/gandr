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
//! thread, one at a time and only when the loop asks for the next, and the
//! loop waits for a frame or the earliest deadline, whichever comes first. The
//! reader reads nothing ahead: a frame is read only once the loop has handled
//! and written everything the frame before owed, so a session over streams
//! stays in lockstep, and the reader is waiting on the loop, never on the
//! stream, whenever the loop returns.
//!
//! - Alternative: a non-blocking stream polled on a timer, which is not
//!   portable to standard input and spends a wake-up per poll.
//! - Reversal: a loop that needs to read ahead, to cancel a recheck a newer
//!   change supersedes, reads ahead on this thread and keeps the deadlines.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::ops::ControlFlow;
use core::time::Duration;
use std::io::BufRead;
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
use crate::server::Logged;
use crate::transport::Body;
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
///   operand's form.
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
/// - witness: `editor::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
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
    /// - witness: `session::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
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
    /// - witness: `session::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
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
pub enum Met
{
    /// A frame the client sent.
    Frame(Body),
    /// A document whose deadline passed.
    Quiet(DocumentUri),
    /// The client's stream closed at a frame boundary.
    Closed,
}

/// Serve `input` through `visit`: each frame read, each deadline passed and
/// the end of the stream, in the order they come, until `visit` breaks.
///
/// # Specification
/// - requires: nothing of the stream.
/// - ensures: a frame is read only after `visit` returned for the one before,
///   on a scoped thread, and handed to `visit` as [`Met::Frame`]; while none
///   arrives, each document whose deadline in the [`Deadlines`] `visit` arms
///   passes is handed to `visit` as [`Met::Quiet`], disarmed; a stream closed
///   at a frame boundary is [`Met::Closed`]. The first break `visit` returns is
///   returned, the reading thread waiting on the loop by then.
/// - provides: the loop of [`crate::serve`] and of each hub connection.
/// - fails: the first [`TransportFault`] of the stream, and the first `visit`
///   returns.
/// - panics: none.
/// - executable: none — the stream is opaque, and what `visit` writes is its
///   own.
///
/// # Errors
/// [`TransportFault`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — every served editor session runs here in lockstep; L3 — a
///   held diagnostic publishes after the interval with no frame sent, and a
///   session ends at `exit` and at a closed stream.
/// - witness: `session::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
/// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `session::session::a_stream_closed_without_exit_ends_abruptly`
#[inline]
pub fn paced<Input, Visit, Ended>(
    input: &mut Input,
    mut visit: Visit,
) -> Result<Ended, TransportFault>
where
    Input: BufRead + Send,
    Visit: FnMut(Met, &mut Deadlines) -> Result<ControlFlow<Ended>, TransportFault>,
{
    std::thread::scope(|scope| {
        let (want, wanted) = mpsc::channel::<()>();
        let (read, frames) = mpsc::channel::<Result<Maybe<Body, _>, TransportFault>>();
        let _reader = scope.spawn(move || {
            for () in wanted {
                let frame = read_frame(input);
                let last = !matches!(frame, Ok(Maybe::Present(_)));
                if read.send(frame).is_err() || last {
                    break;
                }
            }
        });
        let mut deadlines = Deadlines::default();
        loop {
            if want.send(()).is_err() {
                return match visit(Met::Closed, &mut deadlines)? {
                    ControlFlow::Break(ended) => Ok(ended),
                    ControlFlow::Continue(()) => continue,
                };
            }
            let frame = loop {
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
                    Ok(frame) => break frame,
                    Err(RecvTimeoutError::Disconnected) => {
                        break Ok(Maybe::Absent(read_frame::Absent::Closed));
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
            };
            let met = match frame? {
                Maybe::Present(body) => Met::Frame(body),
                Maybe::Absent(_) => Met::Closed,
            };
            if let ControlFlow::Break(ended) = visit(met, &mut deadlines)? {
                return Ok(ended);
            }
        }
    })
}

#[cfg(test)]
mod tests
{
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::caret_form;
    use super::formless;
    use crate::recheck::grammar;

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
    }
}
