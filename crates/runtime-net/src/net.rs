//! The network a run's host holds: an [`Endpoint`] bound on the first
//! operation that needs one, so a program that never reaches the network
//! binds no socket and starts no thread.

use gandr_storage_values::ValueManifest;

use crate::chunks::Chunks;
use crate::chunks::Fetched;
use crate::endpoint::Binding;
use crate::endpoint::Endpoint;
use crate::endpoint::Fault;
use crate::endpoint::Frame;
use crate::endpoint::StreamId;
use crate::peer::NodeId;
use crate::peer::Peer;
use crate::worlds::Answer;
use crate::worlds::Arrival;
use crate::worlds::ArrivalId;
use crate::worlds::Configuration;

/// A host's network: an endpoint bound on first use, then each operation
/// passed to it.
#[derive(Debug)]
pub struct Net
{
    /// What the endpoint binds with.
    binding: Binding,
    /// The endpoint, once bound.
    endpoint: Option<Endpoint>,
}

impl Net
{
    /// The network `binding` describes, bound on its first operation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(binding: Binding) -> Self
    {
        Self {
            binding,
            endpoint: None,
        }
    }

    /// The key this network proves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_id(&self) -> NodeId
    {
        self.binding.node_id()
    }

    /// The chunks this network serves and fetches into, shared with its
    /// endpoint once bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn chunks(&self) -> &Chunks
    {
        self.binding.chunks()
    }

    /// The endpoint, bound now when it is not yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the endpoint this network holds; one bound by this call is
    ///   held from now on, and a binding refused leaves the network unbound, to
    ///   bind on its next operation.
    /// - fails: [`Fault::Bind`] as [`Endpoint::bind`] refuses.
    /// - panics: none.
    /// - executable: none — binding is the operating system's, across the call.
    ///
    /// # Errors
    /// As [`Endpoint::bind`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a network created unbound binds when it first
    ///   accepts, at the socket its binding names, and a dialer reaches it
    ///   there.
    /// - witness: `tests::net::a_network_binds_on_its_first_operation`
    #[inline]
    pub fn endpoint(&mut self) -> Result<&mut Endpoint, Fault>
    {
        if self.endpoint.is_none() {
            self.endpoint = Some(Endpoint::bind(&self.binding)?);
        }
        self.endpoint.as_mut().ok_or(Fault::Driver)
    }

    /// [`Endpoint::connect`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::connect`].
    #[inline]
    pub fn connect(
        &mut self,
        peer: &Peer,
    ) -> Result<StreamId, Fault>
    {
        self.endpoint()?.connect(peer)
    }

    /// [`Endpoint::accept`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::accept`].
    #[inline]
    pub fn accept(&mut self) -> Result<(NodeId, StreamId), Fault>
    {
        self.endpoint()?.accept()
    }

    /// [`Endpoint::send`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::send`].
    #[inline]
    pub fn send(
        &mut self,
        stream: StreamId,
        frame: Frame,
    ) -> Result<(), Fault>
    {
        self.endpoint()?.send(stream, frame)
    }

    /// [`Endpoint::recv`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::recv`].
    #[inline]
    pub fn recv(
        &mut self,
        stream: StreamId,
    ) -> Result<Frame, Fault>
    {
        self.endpoint()?.recv(stream)
    }

    /// [`Endpoint::close`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::close`].
    #[inline]
    pub fn close(
        &mut self,
        stream: StreamId,
    ) -> Result<(), Fault>
    {
        self.endpoint()?.close(stream)
    }

    /// [`Endpoint::migrate`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::migrate`].
    #[inline]
    pub fn migrate(
        &mut self,
        peer: &Peer,
        configuration: &Configuration,
    ) -> Result<Answer, Fault>
    {
        self.endpoint()?.migrate(peer, configuration)
    }

    /// [`Endpoint::arrive`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::arrive`].
    #[inline]
    pub fn arrive(&mut self) -> Result<Arrival, Fault>
    {
        self.endpoint()?.arrive()
    }

    /// [`Endpoint::fetch_arrived`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::fetch_arrived`].
    #[inline]
    pub fn fetch_arrived(
        &mut self,
        arrival: ArrivalId,
        wanted: &ValueManifest,
        held: &[ValueManifest],
    ) -> Result<Fetched, Fault>
    {
        self.endpoint()?.fetch_arrived(arrival, wanted, held)
    }

    /// [`Endpoint::answer`], binding first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::endpoint`] and [`Endpoint::answer`].
    #[inline]
    pub fn answer(
        &mut self,
        arrival: ArrivalId,
        answer: &Answer,
    ) -> Result<(), Fault>
    {
        self.endpoint()?.answer(arrival, answer)
    }
}
