//! The handover between two builds of one session: what a relay that switches
//! builds gives the image it execs.
//!
//! # A session crosses builds as its own messages
//!
//! **Choice.** A relay whose selection moves to another build asks its hub for
//! the connection's replay with the request `gandr/replay`. The hub answers
//! with the messages that open the connection again: the client's
//! `initialize` as the client sent it, `initialized`, and a `didOpen` of each
//! document the connection holds at its text and version. The relay hands
//! that replay to the next image with the frame it held back and every byte
//! it read past that frame. The next image sends the replay to its own
//! build's hub, drops the answer to the replayed `initialize`, and relays the
//! carried bytes before standard input.
//!
//! **Format.** A handover is one frame whose body is the replay as a JSON
//! array of messages, followed by the carried bytes as the client wrote them.
//! Both are Language Server Protocol, so no format of gandr's own has to stay
//! stable across builds.
//!
//! **Alternatives.** The relay could record the opening itself, but the
//! documents' texts would need every change applied a second time, which the
//! hub already does. Passing the handover through an inherited descriptor
//! would spare a file, at the cost of a descriptor the next image must find
//! by number; a file in the hub's private runtime directory is named in one
//! variable. Settings the client changed after `initialize` are not replayed:
//! the next build reads them again when it pulls them.
//!
//! **Reversal.** A client whose settings drift from its `initialize` makes the
//! replay carry the last `workspace/didChangeConfiguration` too.

use std::io;
use std::io::BufRead;
use std::io::Write;

use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::transport::Body;
use crate::transport::TransportFault;
use crate::transport::read_frame;
use crate::transport::write_frame;

/// The method a relay asks its hub for the connection's replay with, and the
/// identifier of the request and of the replayed `initialize`.
pub const REPLAY: &str = "gandr/replay";

/// The client's bytes a relay read and did not forward, the frame it held
/// back first, as the client wrote them.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Carried(pub Vec<u8>);

/// What a relay that switched builds gives the image it execs: the messages
/// that open the connection again, and the client's bytes it read but did not
/// forward.
///
/// # Specification
/// - invariant: each replayed message is one JSON message; the carried bytes
///   are the client's, unread by any hub.
///
/// # Adequacy
/// - hypothesis: L3 — a handover written and read back keeps its replay and
///   carried bytes, and a session opened by a switch's handover goes on in the
///   next relay with the replay's answers dropped.
/// - witness: `handover::tests::a_handover_reads_back_as_written`
/// - witness: `hub::tests::a_relay_switches_once_nothing_is_pending`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Handover
{
    /// The messages that open the connection again, in the order they are
    /// sent.
    replay: Vec<Body>,
    /// The client's bytes read but not forwarded: the frame held back first.
    carried: Carried,
}

impl Handover
{
    /// The handover of `replay` and `carried`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        replay: Vec<Body>,
        carried: Carried,
    ) -> Self
    {
        Self { replay, carried }
    }

    /// The messages that open the connection again.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn replay(&self) -> &[Body]
    {
        &self.replay
    }

    /// The client's bytes read but not forwarded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn carried(&self) -> &Carried
    {
        &self.carried
    }

    /// Write the handover to `output`: the replay as one frame holding a
    /// JSON array, then the carried bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Handover::read`] reads back an equal handover from what was
    ///   written.
    /// - fails: when `output` refuses a write.
    /// - panics: none.
    /// - executable: none — the bytes go to `output`.
    ///
    /// # Errors
    /// [`TransportFault::Io`] when `output` refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `handover::tests::a_handover_reads_back_as_written`
    #[inline]
    pub fn write<Output>(
        &self,
        output: &mut Output,
    ) -> Result<(), TransportFault>
    where
        Output: Write,
    {
        let mut array = Vec::from(*b"[");
        for (place, message) in self.replay.iter().enumerate() {
            if place > 0 {
                array.push(b',');
            }
            array.extend_from_slice(message.as_ref());
        }
        array.push(b']');
        write_frame(output, &Body::from(array))?;
        output
            .write_all(&self.carried.0)
            .map_err(TransportFault::Io)?;
        output.flush().map_err(TransportFault::Io)
    }

    /// Read a handover [`Handover::write`] wrote from `input`, to its end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the replay is the first frame's array, one body per message,
    ///   and the carried bytes are every byte after it.
    /// - fails: when `input` breaks, holds no frame, or its first frame is no
    ///   JSON array.
    /// - panics: none.
    /// - executable: none — the bytes come from `input`.
    ///
    /// # Errors
    /// [`TransportFault`] reading the frame; [`TransportFault::Truncated`]
    /// when `input` holds none; [`TransportFault::Io`] of kind
    /// `InvalidData` when the frame is no JSON array.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `handover::tests::a_handover_reads_back_as_written`
    #[inline]
    pub fn read<Input>(input: &mut Input) -> Result<Self, TransportFault>
    where
        Input: BufRead,
    {
        let Maybe::Present(frame) = read_frame(input)?
        else {
            return Err(TransportFault::Truncated);
        };
        let messages: Vec<Value> = serde_json::from_slice(frame.as_ref()).map_err(|error| {
            TransportFault::Io(io::Error::new(io::ErrorKind::InvalidData, error))
        })?;
        let replay = messages
            .iter()
            .map(|message| serde_json::to_vec(message).map(Body::from))
            .collect::<Result<Vec<Body>, serde_json::Error>>()
            .map_err(TransportFault::Encode)?;
        let mut carried = Vec::new();
        let _read = input
            .read_to_end(&mut carried)
            .map_err(TransportFault::Io)?;
        Ok(Self {
            replay,
            carried: Carried(carried),
        })
    }
}

#[cfg(test)]
mod tests
{
    use super::Carried;
    use super::Handover;
    use crate::transport::Body;

    #[test]
    fn a_handover_reads_back_as_written()
    {
        let handover = Handover::new(
            Vec::from([
                Body::from(
                    br#"{"id":"gandr/replay","jsonrpc":"2.0","method":"initialize","params":{}}"#
                        .to_vec(),
                ),
                Body::from(br#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_vec()),
            ]),
            Carried(b"Content-Length: 2\r\n\r\n{}Content-Le".to_vec()),
        );
        let mut written = Vec::new();
        handover
            .write(&mut written)
            .expect("a vector takes the handover");
        let read = Handover::read(&mut written.as_slice()).expect("the handover reads back");
        assert_eq!(
            read, handover,
            "the replay and the carried bytes, a frame cut short among them"
        );
    }
}
