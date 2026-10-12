//! The hub's render-bus face: a renderer in another process attaches, hears
//! the documents the hub holds, and receives each document's report every
//! time a synchronisation publishes it.

use alloc::string::String;
use alloc::vec::Vec;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::sync::Mutex;
use std::sync::mpsc::channel;
use std::thread;

use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::RenderFrame;

use crate::hub::lock;
use crate::protocol::DocumentUri;
use crate::server::Peer;
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
    /// The client's stream ended, or sent a line that is not a frame.
    Closed,
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
///   greeting naming every document the hub holds, then each one's report;
///   then, for every document a synchronisation publishes, its report at the
///   version published. A resync from the client is answered with the named
///   document's report at its current version, nothing for a document the hub
///   no longer holds; a detach is answered with a detach and ends the face.
///   Frames are written one line each, in the order the face made them. The
///   face returns when the client's stream ends, a line is not a frame, or a
///   write fails.
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
///   connection with another preface is detached at once.
/// - witness: `hub::tests::an_attached_view_follows_the_editors_edits`
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
    let opening = {
        let mut held = lock(workspace);
        held.watch(peer, watcher);
        let mut opening = Vec::from([held.greeting()]);
        let uris: Vec<DocumentUri> = held.held().map(|(uri, _version)| uri.clone()).collect();
        opening.extend(uris.iter().filter_map(|uri| held.rendered(uri)));
        drop(held);
        opening
    };
    if send(&mut writing, &opening).is_err() {
        return;
    }
    let forward = events.clone();
    drop(thread::spawn(move || {
        for uri in changes {
            if forward.send(Event::Changed(uri)).is_err() {
                break;
            }
        }
    }));
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
                | Event::Closed => break,
                | Event::Changed(uri) => (lock(workspace).rendered(&uri), false),
                | Event::Sent(frame) => match (frame.scope(), frame.body()) {
                    | (&FrameScope::Document(ref document), &FrameBody::Resync) => (
                        lock(workspace).rendered(&DocumentUri::from(&document.uri)),
                        false,
                    ),
                    | (_, &FrameBody::Detach) => (Some(RenderFrame::detach()), true),
                    | (
                        _,
                        &(FrameBody::Hello { .. } | FrameBody::Frame { .. } | FrameBody::Resync),
                    ) => (None, false),
                },
            };
            if send(&mut writing, frames.as_slice()).is_err() || ending {
                // The reader is woken by the shutdown and ends the loop.
                drop(writing.shutdown(Shutdown::Both));
                break;
            }
        }
    });
}
