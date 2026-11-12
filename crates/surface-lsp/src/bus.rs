//! The hub's render-bus face: a renderer in another process attaches, hears
//! the documents the hub holds, and receives each document's report and
//! account every time a synchronisation publishes it.
//!
//! # The hub serves the render bus
//!
//! **Choice.** A connection to the hub whose first byte is `r` attaches to the
//! render bus: it opens with the line `render-bus/1`, naming the bus and its
//! wire schema version, and is then served newline-delimited
//! `gandr-surface-render-remote` frames. The face greets it with every document
//! the hub holds and sends each one's report, then a report for every document
//! a synchronisation publishes, at the version published; a resync is answered
//! with the document's current report, a detach with a detach and the end of
//! the connection, and an attach naming another version with a detach at once.
//! A report (`Workspace::rendered`) is read off what the editor shows, never
//! judged again: the held text, the highlighter's spans over it, and one card
//! per published error or warning — the registry code when the diagnostic's
//! code is a registry spelling and `Other` with the vocabulary name leading the
//! message otherwise, its span in bytes, absent for one published at the
//! origin, and the related information as its derivation — with an error mark
//! under each located error and a hole tint under each goal. The face is built
//! in, where the Model Context Protocol face is a parameter, because its frames
//! are this crate's own diagnostics and the seam is already a dependency.
//!
//! Before a report, the face sends the document's account: one card per
//! declaration with a content key, as the hub's tiers hold it
//! (`Workspace::accounted`). The attach and a resync get the whole account.
//! After that, the face sends the edits from the cards it sent last, and
//! nothing when they did not change, so an edit to a comment sends no account
//! frame. An admission that settles the document's kernel tiers sends the
//! edits alone, because the report did not change.
//!
//! The face sends the stack card of a document after its report: the context
//! stack at the cursor that the editor's last signature-help or context-stack
//! request named (`Workspace::stacked`). It sends the card again when the
//! cursor moves and after each publication, and nothing when the frame did not
//! change. A document with no cursor sends no card.
//!
//! A client that sends a trace frame subscribes to the trace layer
//! (`Workspace::trace`): each job of every connection then traces while the
//! client is attached. The face sends it the derivation card of the
//! declaration at the cursor (`Workspace::derived`), each goal and type on one
//! line, cut to the room that the client's columns leave it: at once, then
//! after each publication, each admission and each move of the cursor, and
//! nothing when the frame did not change. So a cursor that moves inside one
//! declaration sends no card. A card holds no layout: an open frame from the
//! client names one node of the card, and the face answers its whole goal laid
//! out at the client's columns (`Workspace::opened`). A client that sends no
//! trace frame is sent no card, and its attachment makes no job trace. A
//! declaration that a job judged before the first trace frame holds no tree,
//! so the first trace frame makes each connection judge its documents again at
//! the trace layer (#6716). A view that attaches after the editor's last job
//! thus hears the card with no edit.
//!
//! A hub that reads a store (`Workspace::stored`) sends its card after the
//! greeting: one row for each value of the store under its data directory,
//! keyed by its content pointer, with the cells that no layer fills yet. The
//! face reads the store again for each renderer that attaches, with no lock
//! of the workspace held, and sends no card after that.
//!
//! In the build with the `instrument` feature, the face also watches the
//! hub's work ledger at the cadence of the rows while the renderer is
//! attached. It folds each tick it hears into the renderer's pane
//! (`activity::Pane`) and sends the pool's activity as one connection-scoped
//! frame, and nothing when the pane did not change. A tick comes while a row
//! holds busy time in its window, so the occupancy moves while no event
//! arrives, and an idle pool sends nothing. Without the feature, the hub
//! traces nothing, and a trace frame changes nothing.
//!
//! **Alternatives.** A report built from the judgement's reports rather than
//! the published diagnostics would carry the typed arguments a card has room
//! for, at the cost of keeping each document's reports beside its diagnostics,
//! or judging again; the cards carry what the editor shows. Goal cards wait on
//! goals whose types the checker spells: a goal travels as a tinted hole mark
//! carrying its message until then. A forgotten document is not announced: the
//! frame set has no closing body, and a view keeps the last report it was sent
//! until another document is checked. Sending the text in every report costs
//! its bytes per publication over a local socket; a renderer holding no buffer
//! of its own cannot place a byte range without it.
//!
//! **Reversal.** A view that must show unsaved goals with their types reads
//! goal cards once the checker spells them; a frame set that gains a closing
//! body announces a forgotten document; a report measured as too large for a
//! document's every edit sends only what changed; a pane measured as too
//! large for a tick sends the rows that changed; a store that the engine
//! writes while a renderer is attached sends its card again after each write.

use alloc::collections::BTreeMap;
use alloc::string::String;
#[cfg(feature = "instrument")]
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::sync::Mutex;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::channel;
use std::thread;

use gandr_surface_render_remote::AccountCard;
use gandr_surface_render_remote::AccountKey;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::NodeAt;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::account_edits;

#[cfg(feature = "instrument")]
use crate::activity::Cadence;
#[cfg(feature = "instrument")]
use crate::activity::Pane;
#[cfg(feature = "instrument")]
use crate::activity::Tick;
use crate::hub::lock;
use crate::protocol::DocumentUri;
use crate::server::Peer;
use crate::server::Settlement;
use crate::server::Workspace;

/// The line a render-bus client opens its connection with: the attach, naming
/// the bus and its wire schema version.
pub const RENDER_BUS_PREFACE: &str = "render-bus/1\n";

/// What the face's loop acts on next.
enum Event
{
    /// A frame the client sent.
    Sent(RenderFrame),
    /// A document a synchronisation published or the hub forgot.
    Changed(DocumentUri),
    /// A document whose kernel tiers an admission settled.
    Settled(DocumentUri),
    /// A document whose cursor a request moved.
    Moved(DocumentUri),
    /// A tick of the hub's work ledger that moves the activity pane.
    #[cfg(feature = "instrument")]
    Ticked(Arc<Tick>),
    /// The client's stream ended, or sent a line that is not a frame.
    Closed,
}

/// A channel of documents the workspace names, with the event the face's loop
/// hears for each.
type Forwarded = (Receiver<DocumentUri>, fn(DocumentUri) -> Event);

/// The account frame that takes a renderer from the cards it was sent of the
/// document at `uri`, which `sent` holds, to `account`, the document's
/// account now: the whole account when `whole` asks for it, the patch
/// otherwise, and none for an unchanged account or a forgotten document.
/// `sent` then holds the cards that the renderer holds.
///
/// # Specification
/// trivial.
fn patched(
    account: Option<(DocId, Vec<AccountCard>)>,
    uri: &DocumentUri,
    sent: &mut BTreeMap<DocumentUri, Vec<AccountCard>>,
    whole: Whole,
) -> Option<RenderFrame>
{
    let Some((document, cards)) = account
    else {
        drop(sent.remove(uri));
        return None;
    };
    let held = sent.entry(uri.clone()).or_default();
    let frame = match whole {
        Whole::Asked => RenderFrame::accounts(document, cards.clone()),
        Whole::Owed => {
            let edits = account_edits(held, &cards);
            if edits.is_empty() {
                return None;
            }
            RenderFrame::account_patch(document, edits)
        },
    };
    *held = cards;
    Some(frame)
}

/// The frame of the document at `uri` when it differs from the one `shown`
/// holds for it, which `shown` then holds; none when it is the same, and none
/// for a document with no frame, whose frame `shown` lets go.
///
/// # Specification
/// trivial.
fn renewed(
    frame: Option<RenderFrame>,
    uri: &DocumentUri,
    shown: &mut BTreeMap<DocumentUri, RenderFrame>,
) -> Option<RenderFrame>
{
    let Some(frame) = frame
    else {
        drop(shown.remove(uri));
        return None;
    };
    if shown.get(uri) == Some(&frame) {
        return None;
    }
    drop(shown.insert(uri.clone(), frame.clone()));
    Some(frame)
}

/// Whether a renderer asks for a whole account or is owed the patch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Whole
{
    /// The renderer attached or fell behind: it holds no cards to patch.
    Asked,
    /// The renderer holds the cards it was sent last.
    Owed,
}

/// Write `frames`, one line each, to `writing`.
///
/// # Specification
/// trivial.
fn send(
    writing: &mut UnixStream,
    frames: &[RenderFrame],
) -> io::Result<()>
{
    for frame in frames {
        let mut line = serde_json::to_string(frame).map_err(io::Error::other)?;
        line.push('\n');
        writing.write_all(line.as_bytes())?;
    }
    writing.flush()
}

/// Serve the render bus on the connection `reading` buffers, as `peer`, over
/// `workspace`.
///
/// # Specification
/// - requires: `reading` is the connection the hub accepted, its first byte
///   `r`.
/// - ensures: a connection whose first line is not [`RENDER_BUS_PREFACE`] is
///   answered with a detach and nothing else. Otherwise the face sends the
///   greeting naming every document the hub holds, then the store card when the
///   workspace reads a store, then each document's whole account, its report
///   and its stack card. Then, for every document a synchronisation publishes,
///   it sends the patch of its account when the account changed, its report at
///   the version published, and its stack card when the card frame changed. For
///   every document whose kernel tiers an admission settled, it sends the patch
///   alone, when the account changed. For every document whose cursor a request
///   moved, it sends the stack card when the card frame changed. A resync from
///   the client is answered with the named document's whole account, its report
///   at its current version and its stack card, nothing for a document the hub
///   does not hold; a detach is answered with a detach and ends the face. In
///   the build with the `instrument` feature, a trace frame subscribes the
///   client to the trace layer, and the first one makes every connection judge
///   its documents again at that layer; after it, each of those events and the
///   trace frame itself also send the derivation card at the document's cursor
///   when its frame changed, and a resync sends it whole. An open frame from a
///   subscribed client is answered with the whole goal of the node it names,
///   absent when the card at the cursor has another key or the node has no
///   goal; an open frame from any other client is answered with nothing. Frames
///   are written one line each, in the order the face made them. In the build
///   with the `instrument` feature, each tick of the hub's work ledger that
///   changes the pane sends the pool's activity, connection-scoped, and a tick
///   that leaves it as it was sends nothing. The face returns when the client's
///   stream ends, a line is not a frame, or a write fails.
/// - provides: `gandr serve`'s render-bus face, which `gandr view` attaches to.
/// - fails: never; a fault ends the connection.
/// - panics: none.
/// - executable: none — the effects are lines on a socket and a watcher in a
///   workspace other connections change concurrently.
///
/// # Adequacy
/// - hypothesis: L3 — through a running hub, a view attached beside an editor
///   receives the greeting and the held document's report, the next version's
///   report after the editor's edit, a resync's answer and the detach; a
///   connection with another preface is detached at once. The view receives the
///   document's whole account, a patch once the admission settles it, and no
///   patch after an edit to a comment. In the build with the `instrument`
///   feature, the edit's judgement shows in the pool's activity, each frame
///   differs from the one before, and the pane goes back to idle once the busy
///   time leaves the window. The view hears the stack card at the cursor the
///   editor's signature help names, and a card again after an edit changes it.
///   A view of the trace layer hears the derivation card of the declaration at
///   that cursor with no edit, each row on one line in its room, the whole goal
///   of the node it opens, and nothing while the cursor moves inside it. A view
///   of a hub that reads a store hears its card after the greeting.
/// - witness: `hub::tests::an_attached_view_follows_the_editors_edits`
/// - witness: `hub::tests::an_attached_view_follows_the_accounts_of_the_editors_document`
/// - witness: `hub::tests::an_attached_view_hears_the_pool_at_work`
/// - witness: `hub::tests::an_attached_view_follows_the_stack_at_the_editors_cursor`
/// - witness: `hub::tests::an_attached_view_follows_the_derivation_at_the_editors_cursor_6716_6930`
/// - witness: `hub::tests::an_attached_view_hears_the_store_6296`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the change, settlement and tick forwarders and the view's line reader each block on their channel or socket for the attachment's life"
    )
)]
#[inline]
pub fn serve(
    reading: &mut BufReader<UnixStream>,
    peer: Peer,
    workspace: &Mutex<Workspace>,
)
{
    let Ok(mut writing) = reading.get_ref().try_clone()
    else {
        return;
    };
    let mut preface = String::new();
    if reading.read_line(&mut preface).is_err() || preface != RENDER_BUS_PREFACE {
        drop(send(&mut writing, &[RenderFrame::detach()]));
        return;
    }
    let (events, inbox) = channel();
    let (watcher, changes) = channel::<DocumentUri>();
    let (accountant, settlements) = channel::<DocumentUri>();
    let (stacker, moves) = channel::<DocumentUri>();
    #[cfg(feature = "instrument")]
    let (ticker, ticks) = channel::<Arc<Tick>>();
    // The cards each document's last account frame left the renderer with.
    let mut sent: BTreeMap<DocumentUri, Vec<AccountCard>> = BTreeMap::new();
    // The last stack frame each document sent.
    let mut stacks: BTreeMap<DocumentUri, RenderFrame> = BTreeMap::new();
    // The columns of a client of the trace layer, and the last derivation
    // frame each document sent it.
    let mut traced: Option<Count> = None;
    let mut derivations: BTreeMap<DocumentUri, RenderFrame> = BTreeMap::new();
    // The store is read with no lock of the workspace held: a reading opens
    // the store and walks the closure of each value it did not read yet.
    let store = lock(workspace)
        .stored()
        .map(|(stored, paths)| RenderFrame::store(stored.card(&paths)));
    let opening = {
        let mut held = lock(workspace);
        held.watch(peer, watcher);
        held.watch_accounts(peer, accountant);
        held.watch_stacks(peer, stacker);
        // A host that refuses the fold's thread leaves the pane out; the
        // reports go on.
        #[cfg(feature = "instrument")]
        drop(held.activity().watch(peer, ticker, Cadence::Rows));
        let mut opening = Vec::from([held.greeting()]);
        opening.extend(store);
        let uris: Vec<DocumentUri> = held.held().map(|(uri, _version)| uri.clone()).collect();
        for uri in &uris {
            opening.extend(patched(held.accounted(uri), uri, &mut sent, Whole::Asked));
            opening.extend(held.rendered(uri));
            opening.extend(renewed(held.stacked(uri), uri, &mut stacks));
        }
        drop(held);
        opening
    };
    if send(&mut writing, &opening).is_err() {
        return;
    }
    #[cfg(feature = "instrument")]
    {
        let forward = events.clone();
        drop(thread::spawn(move || {
            for tick in ticks {
                if forward.send(Event::Ticked(tick)).is_err() {
                    break;
                }
            }
        }));
    }
    // The pane of the pool, and the last activity frame the renderer holds.
    #[cfg(feature = "instrument")]
    let (mut pane, mut shown) = (Pane::default(), None::<RenderFrame>);
    let forwarded: [Forwarded; 3] = [
        (changes, Event::Changed),
        (settlements, Event::Settled),
        (moves, Event::Moved),
    ];
    for (heard, event) in forwarded {
        let forward = events.clone();
        drop(thread::spawn(move || {
            for uri in heard {
                if forward.send(event(uri)).is_err() {
                    break;
                }
            }
        }));
    }
    thread::scope(|scope| {
        drop(scope.spawn(move || {
            let mut line = String::new();
            while reading.read_line(&mut line).is_ok_and(|read| read != 0) {
                let Ok(frame) = serde_json::from_str::<RenderFrame>(&line)
                else {
                    break;
                };
                line.clear();
                if events.send(Event::Sent(frame)).is_err() {
                    return;
                }
            }
            drop(events.send(Event::Closed));
        }));
        for event in &inbox {
            let (frames, ending) = match event {
                Event::Closed => break,
                Event::Changed(uri) => {
                    let held = lock(workspace);
                    let (account, report, card, derivation) = (
                        held.accounted(&uri),
                        held.rendered(&uri),
                        held.stacked(&uri),
                        derived(&held, &uri, traced),
                    );
                    drop(held);
                    let patch = patched(account, &uri, &mut sent, Whole::Owed);
                    let card = renewed(card, &uri, &mut stacks);
                    let derivation = rederived(derivation, &uri, &mut derivations);
                    (
                        patch
                            .into_iter()
                            .chain(report)
                            .chain(card)
                            .chain(derivation)
                            .collect(),
                        false,
                    )
                },
                Event::Settled(uri) => {
                    let held = lock(workspace);
                    let (account, derivation) =
                        (held.accounted(&uri), derived(&held, &uri, traced));
                    drop(held);
                    let patch = patched(account, &uri, &mut sent, Whole::Owed);
                    let derivation = rederived(derivation, &uri, &mut derivations);
                    (patch.into_iter().chain(derivation).collect(), false)
                },
                Event::Moved(uri) => {
                    let held = lock(workspace);
                    let (card, derivation) = (held.stacked(&uri), derived(&held, &uri, traced));
                    drop(held);
                    let card = renewed(card, &uri, &mut stacks);
                    let derivation = rederived(derivation, &uri, &mut derivations);
                    (card.into_iter().chain(derivation).collect(), false)
                },
                #[cfg(feature = "instrument")]
                Event::Ticked(tick) => {
                    let frame = RenderFrame::activity(pane.hear(&tick));
                    if shown.as_ref() == Some(&frame) {
                        (Vec::new(), false)
                    }
                    else {
                        let failed = send(&mut writing, core::slice::from_ref(&frame)).is_err();
                        shown = Some(frame);
                        (Vec::new(), failed)
                    }
                },
                Event::Sent(frame) => match (frame.scope(), frame.body()) {
                    (&FrameScope::Document(ref document), &FrameBody::Resync) => {
                        let uri = DocumentUri::from(&document.uri);
                        let held = lock(workspace);
                        let (account, report, card, derivation) = (
                            held.accounted(&uri),
                            held.rendered(&uri),
                            held.stacked(&uri),
                            derived(&held, &uri, traced),
                        );
                        drop(held);
                        let whole = patched(account, &uri, &mut sent, Whole::Asked);
                        drop(stacks.remove(&uri));
                        let card = renewed(card, &uri, &mut stacks);
                        drop(derivations.remove(&uri));
                        let derivation = rederived(derivation, &uri, &mut derivations);
                        (
                            whole
                                .into_iter()
                                .chain(report)
                                .chain(card)
                                .chain(derivation)
                                .collect(),
                            false,
                        )
                    },
                    (_, &FrameBody::Trace { columns }) => {
                        traced = Some(columns);
                        derivations.clear();
                        let mut held = lock(workspace);
                        subscribe(&mut held, peer);
                        let frames = held
                            .held()
                            .filter_map(|(uri, _version)| {
                                rederived(derived(&held, uri, traced), uri, &mut derivations)
                            })
                            .collect();
                        drop(held);
                        (frames, false)
                    },
                    (&FrameScope::Document(ref document), &FrameBody::Open { ref key, at }) => {
                        let uri = DocumentUri::from(&document.uri);
                        let held = lock(workspace);
                        let answer = opened(&held, &uri, (key, at), traced);
                        drop(held);
                        (answer.into_iter().collect(), false)
                    },
                    (_, &FrameBody::Detach) => (Vec::from([RenderFrame::detach()]), true),
                    (
                        _,
                        &(FrameBody::Hello { .. }
                        | FrameBody::Frame { .. }
                        | FrameBody::Resync
                        | FrameBody::Accounts { .. }
                        | FrameBody::AccountPatch { .. }
                        | FrameBody::Stack { .. }
                        | FrameBody::Derivation { .. }
                        | FrameBody::Open { .. }
                        | FrameBody::Opened { .. }
                        | FrameBody::Activity { .. }
                        | FrameBody::Store { .. }),
                    ) => (Vec::new(), false),
                },
            };
            if send(&mut writing, &frames).is_err() || ending {
                // The reader is woken by the shutdown and ends the loop.
                drop(writing.shutdown(Shutdown::Both));
                break;
            }
        }
    });
}

/// What the face reads of the derivation of a document for a client of the
/// trace layer.
enum Derived
{
    /// The document's judgement runs: its tiers name the declarations of the
    /// text before the edit, so the client keeps the card it holds (#6930).
    Held,
    /// The document's derivation frame, or none to show.
    Read(Option<RenderFrame>),
}

/// The derivation of the document at `uri` for a client of the trace layer
/// whose panes are `columns` wide.
///
/// # Specification
/// trivial.
fn derived(
    held: &Workspace,
    uri: &DocumentUri,
    columns: Option<Count>,
) -> Derived
{
    match held.settled(uri) {
        Settlement::Settled => Derived::Read(derivation(held, uri, columns)),
        Settlement::Running => Derived::Held,
    }
}

/// The frame of `found` for the document at `uri` when it differs from the
/// one `shown` holds, as [`renewed`] gives it; none while the document's
/// judgement runs, and `shown` keeps its frame.
///
/// # Specification
/// trivial.
fn rederived(
    found: Derived,
    uri: &DocumentUri,
    shown: &mut BTreeMap<DocumentUri, RenderFrame>,
) -> Option<RenderFrame>
{
    match found {
        Derived::Held => None,
        Derived::Read(frame) => renewed(frame, uri, shown),
    }
}

/// The derivation frame of the document at `uri` for a client of the trace
/// layer whose panes are `columns` wide: none for a client that did not
/// subscribe.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
fn derivation(
    held: &Workspace,
    uri: &DocumentUri,
    columns: Option<Count>,
) -> Option<RenderFrame>
{
    held.derived(uri, columns?)
}

/// None: without the `instrument` feature the hub traces nothing, so no
/// client is sent a derivation frame.
///
/// # Specification
/// trivial.
#[cfg(not(feature = "instrument"))]
const fn derivation(
    _held: &Workspace,
    _uri: &DocumentUri,
    _columns: Option<Count>,
) -> Option<RenderFrame>
{
    None
}

/// The answer to a client of the trace layer, whose panes are `columns` wide,
/// that opens the node at `at` of the card keyed `key` of the document at
/// `uri`: none for a client that did not subscribe.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
fn opened(
    held: &Workspace,
    uri: &DocumentUri,
    (key, at): (&AccountKey, NodeAt),
    columns: Option<Count>,
) -> Option<RenderFrame>
{
    held.opened(uri, (key, at), columns?)
}

/// None: without the `instrument` feature the hub sends no derivation card, so
/// no client opens a node of one.
///
/// # Specification
/// trivial.
#[cfg(not(feature = "instrument"))]
const fn opened(
    _held: &Workspace,
    _uri: &DocumentUri,
    _node: (&AccountKey, NodeAt),
    _columns: Option<Count>,
) -> Option<RenderFrame>
{
    None
}

/// Subscribe `peer` to the trace layer of `held`.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
fn subscribe(
    held: &mut Workspace,
    peer: Peer,
)
{
    held.trace(peer);
}

/// Nothing: without the `instrument` feature the hub has no trace layer.
///
/// # Specification
/// trivial.
#[cfg(not(feature = "instrument"))]
const fn subscribe(
    _held: &mut Workspace,
    _peer: Peer,
)
{
}
