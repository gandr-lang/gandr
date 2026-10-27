//! The host seam: an operation no handler of the run claims is offered to
//! the caller's host, which resumes the run with a reply, stops it, or
//! declines and leaves the operation unhandled.
//!
//! An operation is offered where the nearest delimiter does not claim it —
//! no delimiter at all, a handler of another interface, a reset — and where
//! an exercise names a capability no handler of the run introduced. The
//! payload is moved into the caller's store and offered with the
//! operation's inline interface; [`HostValues`] lets the host inspect it,
//! allocate a reply over it, read either back and move either across by
//! content, never touch a frame. A reply resumes the operation's
//! continuation once: the host call answers it, and the perform's
//! continuation receives it as any value. A reply naming a value the run
//! moved out is that value again — a thunk or a function keeps its identity
//! — and a reply the host built is laid out on the run's heap as the run
//! lays out its own. [`HostReply::Abort`] stops the run without resuming;
//! [`HostReply::Decline`] leaves
//! [`Stuck::PerformNoHandler`](gandr_core_sequent::Stuck::PerformNoHandler)
//! at the operation. The host owns external effects, reply typing and
//! policy; a run performs no host I/O itself.
//!
//! A run's regions are allocated at their bounds before it starts, so a run
//! never repeats from its start and the host sees each operation once.
//!
//! **Choice.** The seam is the host-call stencil every primitive and control
//! operation already takes, so both tiers offer through one Rust function.
//! **Alternative.** A seam of its own beside the stencils, which would hand
//! the host a second calling convention for the same frames. **Reversal.**
//! A host that must observe or alter frames — a debugger — needs a frame
//! capability this seam does not grant.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: integrity never
//!   substitutes validity, § kernel-verdict-reuse: a reply a host derefs from
//!   chunks is the value their digests name, and that it has the operation's
//!   reply type stays the host's obligation, as for any reply.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::Store;
use gandr_core_sequent::StoreFault;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::ValueManifest;

use crate::crossing;
use crate::crossing::CrossingRefusal;

/// An operation no handler of the run claims.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct HostRequest<'request>
{
    /// The inline interface; its type handles belong to
    /// [`HostValues::annotations`].
    pub signature: &'request EffectSig,
    /// The requested operation within that interface.
    pub operation: &'request OperationName,
    /// The payload, moved into the caller's store.
    pub payload: HeapValueId,
}

/// A host's decision about one offered operation.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostReply<Abort>
{
    /// Deliver a value of the caller's store to the operation's
    /// continuation.
    Resume(HeapValueId),
    /// Stop without resuming, carrying the host's termination result.
    Abort(Abort),
    /// Leave the operation unhandled, the run stuck at it.
    Decline,
}

/// How a run with a host ended.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostOutcome<Abort>
{
    /// The run halted or stopped stuck.
    Completed(Outcome),
    /// The host stopped the run instead of replying.
    Aborted(Abort),
}

/// Decides the operations a run offers, without access to its frames.
pub trait HostHandler
{
    /// The host's non-resuming termination result, such as a process exit
    /// code.
    type Abort;

    /// Decide one unclaimed operation; an operation a handler of the run
    /// claims never reaches this.
    ///
    /// # Specification
    /// - requires: a resumed value is one of `values`' store and has the
    ///   operation's reply type. The host owns external effects and policy.
    /// - ensures: a reply continues the operation's continuation, an abort
    ///   stops the run, and a decline leaves the operation unhandled. A run
    ///   never offers the same operation twice.
    /// - executable: none — the trait states the host's obligation; each body
    ///   is an implementor's, and the run checks the reply it receives.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scripted hosts that resume, abort and decline,
    ///   offered operations claimed and unclaimed by the run's handlers,
    ///   separate a retried, misrouted or silently dropped decision.
    /// - witness: `tests::seam::a_host_resumes_a_single_unhandled_perform`
    /// - witness: `tests::seam::a_host_decline_blames_the_perform`
    /// - witness: `tests::seam::a_host_is_never_offered_a_claimed_perform`
    /// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>;
}

/// The host's value capability over the caller's store: inspect, allocate,
/// read back and cross by content, never alter frames.
#[derive(Debug)]
pub struct HostValues<'run>
{
    /// The run's IL, which owns the interfaces' type handles.
    arena: &'run CommandArena,
    /// The caller's store.
    store: &'run mut Store,
}

impl<'run> HostValues<'run>
{
    /// The capability over `store` for a run of `arena`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        arena: &'run CommandArena,
        store: &'run mut Store,
    ) -> Self
    {
        Self { arena, store }
    }

    /// The arena owning the offered interface's type handles.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn annotations(&self) -> &CoreArena
    {
        self.arena.annotations()
    }

    /// Inspect an offered payload or a reply allocated before.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        value: HeapValueId,
    ) -> Option<&HeapValue>
    {
        self.store.value(value)
    }

    /// Allocate a reply node over values the store holds.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The store's refusal: its address space is spent.
    #[inline]
    pub fn allocate(
        &mut self,
        value: HeapValue,
    ) -> Result<HeapValueId, StoreFault>
    {
        self.store.allocate(value)
    }

    /// Read a value back as a core value, closing captured thunks and
    /// functions over their environments.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The readback's refusal: a dangling value, a suspended capture or a
    /// stack with no literal spelling; no placeholder is read.
    #[inline]
    pub fn read_back_value(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ValueId, ReadbackRefusal>
    {
        read_back_value(self.arena, self.store, value, core)
    }

    /// Commit a value the store holds, a payload or a reply allocated
    /// before, to `chunks` under the crossing's profile at `params`: the
    /// value leaves the run by content, as [`crossing::commit`] writes it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`crossing::commit`]'s refusal: a value that does not cross is named,
    /// and nothing is written.
    #[inline]
    pub fn commit<Chunks>(
        &self,
        value: HeapValueId,
        params: TypedChunkerParams,
        chunks: &mut Chunks,
    ) -> Result<ValueManifest, CrossingRefusal>
    where
        Chunks: ChunkStore + ?Sized,
    {
        crossing::commit(self.store, value, params, chunks)
    }

    /// Read the value `manifest` commits out of `chunks` into the store, at
    /// addresses fresh there, as [`crossing::deref()`] lays it: a reply the
    /// host may resume with.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`crossing::deref()`]'s refusal: a profile other than the crossing's
    /// at `params`, a chunk `chunks` lacks or refuses, or an allocation the
    /// store refuses.
    #[inline]
    pub fn deref(
        &mut self,
        manifest: &ValueManifest,
        params: TypedChunkerParams,
        chunks: &dyn ChunkStore,
    ) -> Result<HeapValueId, CrossingRefusal>
    {
        crossing::deref(manifest, params, chunks, self.store)
    }
}

/// A host's decision with its abort result kept by the adapter: what the
/// host call reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Offered
{
    /// Resume with this value of the store.
    Resume(HeapValueId),
    /// The host stopped the run.
    Abort,
    /// The operation stays unhandled.
    Decline,
}

/// A host the host-call entry can hold behind one pointer, whatever its
/// abort result.
pub trait Offer
{
    /// Offer one operation.
    ///
    /// # Specification
    /// trivial.
    fn offer(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> Offered;
}

/// A host and the abort result it stopped the run with, if it did.
#[derive(Debug)]
pub struct Adapter<'host, Host>
where
    Host: HostHandler,
{
    /// The host.
    pub host: &'host mut Host,
    /// What the host aborted with.
    pub aborted: Option<Host::Abort>,
}

impl<Host> Offer for Adapter<'_, Host>
where
    Host: HostHandler,
{
    /// Offer to the host, keeping an abort's result.
    ///
    /// # Specification
    /// trivial.
    fn offer(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> Offered
    {
        match self.host.handle(request, values) {
            HostReply::Resume(value) => Offered::Resume(value),
            HostReply::Abort(abort) => {
                self.aborted = Some(abort);
                Offered::Abort
            },
            HostReply::Decline => Offered::Decline,
        }
    }
}
