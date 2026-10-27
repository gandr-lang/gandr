//! The chunk wire on loopback: a holder serves what its run committed while
//! its owner waits on nothing, a second fetch of an edited value carries only
//! the chunks the edit added, and an answer that does not verify, does not
//! frame or does not hold the value whole is refused.

use core::net::IpAddr;
use core::net::Ipv4Addr;
use core::net::SocketAddr;
use std::thread;

use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::crossing::commit;
use gandr_runtime_emitter::crossing::deref;
use gandr_runtime_net::Binding;
use gandr_runtime_net::CHUNKS_ALPN;
use gandr_runtime_net::Chunks;
use gandr_runtime_net::Endpoint;
use gandr_runtime_net::Fault;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::EditDepth;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::expected_chunk_bound;
use gandr_storage_values::measure_edit;

/// A list of this many integers commits to a few hundred chunks under
/// [`params`], some 58 KiB of images.
const LENGTH: u64 = 888;

/// The element the edit replaces, halfway along the list.
const EDITED: u64 = 444;

/// The most bytes a forged holder reads of a request.
const REQUEST_BYTES: usize = 0x0010_0000;

/// The chunker's constants both ends commit and read under.
///
/// # Specification
/// trivial.
fn params() -> TypedChunkerParams
{
    TypedChunkerParams::new(
        Kappa::try_from(4_u64).expect("nonzero kappa"),
        TokenCap::try_from(64_u64).expect("nonzero cap"),
    )
}

/// An endpoint bound on loopback at an ephemeral port, serving `chunks`.
///
/// # Specification
/// trivial.
fn on_loopback(chunks: &Chunks) -> Endpoint
{
    Endpoint::bind(
        &Binding::new(Secret::generate())
            .at(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
            .serving(chunks.clone()),
    )
    .expect("loopback binds")
}

/// `endpoint` as a peer dials it, at its IPv4 socket.
///
/// # Specification
/// trivial.
fn peer_of(endpoint: &Endpoint) -> Peer
{
    let socket = endpoint
        .sockets()
        .iter()
        .copied()
        .find(|socket| socket.ip() == IpAddr::V4(Ipv4Addr::LOCALHOST))
        .expect("an endpoint bound on loopback reports the socket");
    Peer::new(endpoint.node_id()).at(socket)
}

/// The list `[0, 1, …]` of `LENGTH` integers in `store`, the element at
/// `EDITED` replaced by zero when `edited` says so.
///
/// # Specification
/// trivial.
fn list(
    store: &mut Store,
    edited: Edited,
) -> HeapValueId
{
    let mut tail = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::ListNil,
            fields: Box::new([]),
        })
        .expect("room");
    for index in (0 .. LENGTH).rev() {
        let value = if edited == Edited::Yes && index == EDITED {
            0
        }
        else {
            index.saturating_add(1)
        };
        let element = store
            .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
                Sign::NonNegative,
                Magnitude::from_decimal_text(value.to_string()).expect("digits"),
            ))))
            .expect("room");
        tail = store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::ListCons,
                fields: Box::new([element, tail]),
            })
            .expect("room");
    }
    tail
}

/// Whether a list carries the edit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Edited
{
    /// The element at `EDITED` is zero.
    Yes,
    /// Every element is its index plus one.
    No,
}

/// The root `manifest`'s value commits to once read back out of `chunks`:
/// equal values commit to one root, so the root names the value read.
///
/// # Specification
/// trivial.
fn read_back(
    chunks: &Chunks,
    manifest: &ValueManifest,
) -> ContentPtr
{
    let mut store = Store::new();
    let value = deref(manifest, params(), &*chunks.lock(), &mut store).expect("the value derefs");
    commit(&store, value, params(), &mut InMemoryChunkStore::new())
        .expect("the value read back commits")
        .root()
}

#[test]
fn a_second_fetch_carries_only_the_chunks_an_edit_changed()
{
    let at_holder = Chunks::new();
    let at_asker = Chunks::new();
    let holder = on_loopback(&at_holder);
    let mut asker = on_loopback(&at_asker);
    let reached = peer_of(&holder);
    let mut values = Store::new();
    let original = list(&mut values, Edited::No);
    let first = commit(&values, original, params(), &mut *at_holder.lock()).expect("crosses");
    let whole = first
        .closure(&*at_holder.lock())
        .expect("the holder holds what it committed")
        .chunk_count();
    let fetched = asker
        .fetch(&reached, &first, &[])
        .expect("the value is fetched");
    assert_eq!(
        fetched.chunks, whole,
        "a first fetch carries the whole closure"
    );
    assert_eq!(
        read_back(&at_asker, &first),
        first.root(),
        "it reads back equal"
    );
    let edited = list(&mut values, Edited::Yes);
    let second = commit(&values, edited, params(), &mut *at_holder.lock()).expect("crosses");
    let depth = EditDepth::from(EDITED.saturating_add(1));
    let measured = measure_edit(&*at_holder.lock(), first.root(), second.root(), depth)
        .expect("the edit is measured");
    let fetched = asker
        .fetch(&reached, &second, &[first])
        .expect("the edited value is fetched");
    assert_eq!(
        fetched.chunks, measured.chunks_affected,
        "naming the first as held, the second fetch carries exactly the chunks the edit added"
    );
    assert!(
        fetched.chunks < whole,
        "{fetched:?} carries less than the whole of {whole:?}"
    );
    let bound = expected_chunk_bound(depth, &params()).expect("the bound");
    assert!(
        u64::try_from(usize::from(fetched.chunks)).expect("a count") <= u64::from(bound),
        "{fetched:?} sits inside the locality bound {bound:?}"
    );
    assert_eq!(
        read_back(&at_asker, &second),
        second.root(),
        "the edited value reads back equal"
    );
}

/// A holder bound on loopback that answers each fetch with the next of
/// `answers`, written whole, on a thread of its own; its peer and the thread.
///
/// # Specification
/// trivial.
fn forged_holder(answers: Vec<Forged>) -> (Peer, thread::JoinHandle<()>)
{
    let secret = iroh::SecretKey::generate();
    let peer = NodeId::from(secret.public());
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("a runtime");
    let endpoint = runtime
        .block_on(
            iroh::Endpoint::builder(iroh::endpoint::presets::Minimal)
                .secret_key(secret)
                .alpns(Vec::from([CHUNKS_ALPN.to_vec()]))
                .relay_mode(iroh::RelayMode::Disabled)
                .bind_addr(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
                .expect("a loopback socket")
                .bind(),
        )
        .expect("the forged holder binds");
    let socket = endpoint
        .bound_sockets()
        .into_iter()
        .find(|socket| socket.ip() == IpAddr::V4(Ipv4Addr::LOCALHOST))
        .expect("the forged holder reports its socket");
    let serving = thread::spawn(move || {
        runtime.block_on(async move {
            for Forged(answer) in answers {
                let incoming = endpoint.accept().await.expect("a fetch arrives");
                let connection = incoming.await.expect("the handshake completes");
                let (mut send, mut recv) = connection.accept_bi().await.expect("a stream");
                recv.read_to_end(REQUEST_BYTES).await.expect("the request");
                send.write_all(&answer)
                    .await
                    .expect("the answer is written");
                send.finish().expect("the answer ends");
                match send.stopped().await {
                    Ok(_) | Err(_) => {},
                }
            }
            endpoint.close().await;
        });
    });
    (Peer::new(peer).at(socket), serving)
}

/// The bytes a forged holder answers a fetch with.
#[derive(Clone, Debug, Default)]
#[repr(transparent)]
struct Forged(Vec<u8>);

impl Forged
{
    /// The answer with one more part: `digest`, then `image`.
    ///
    /// # Specification
    /// trivial.
    fn chunk(
        mut self,
        digest: ChunkDigest,
        image: ChunkImage<'_>,
    ) -> Self
    {
        let image: &[u8] = image.into();
        let length = digest.as_ref().len().saturating_add(image.len());
        let length = u32::try_from(length).expect("a short part");
        self.0.extend_from_slice(&length.to_le_bytes());
        self.0.extend_from_slice(digest.as_ref());
        self.0.extend_from_slice(image);
        self
    }

    /// An answer whose one part is three bytes, shorter than a digest.
    ///
    /// # Specification
    /// trivial.
    fn unframed() -> Self
    {
        let mut bytes = 3_u32.to_le_bytes().to_vec();
        bytes.extend([0_u8; 3]);
        Self(bytes)
    }
}

#[test]
fn an_answer_that_does_not_verify_or_frame_is_refused_before_any_chunk_is_kept()
{
    let mut committed = InMemoryChunkStore::new();
    let mut values = Store::new();
    let original = list(&mut values, Edited::No);
    let manifest = commit(&values, original, params(), &mut committed).expect("crosses");
    let mut digests = manifest
        .closure(&committed)
        .expect("held")
        .digests()
        .clone()
        .into_iter();
    let (Some(kept), Some(tampered)) = (digests.next(), digests.next())
    else {
        panic!("the list commits to two chunks at least");
    };
    let mut forged: Vec<u8> = {
        let image: &[u8] = committed.load(tampered).expect("held").image().into();
        image.to_vec()
    };
    let last = forged.last_mut().expect("a nonempty image");
    *last ^= 1;
    let unverified = Forged::default()
        .chunk(kept, committed.load(kept).expect("held").image())
        .chunk(tampered, ChunkImage::from(forged.as_slice()));
    let (holder, serving) = forged_holder(Vec::from([unverified, Forged::unframed()]));
    let at_asker = Chunks::new();
    let mut asker = on_loopback(&at_asker);
    let refused = asker.fetch(&holder, &manifest, &[]);
    assert!(
        matches!(
            refused,
            Err(Fault::Refused { peer, refusal: ValueError::DigestMismatch { expected, .. } })
                if peer == holder.id() && expected == tampered
        ),
        "a chunk not what its digest names is refused by it: {refused:?}"
    );
    assert_eq!(
        at_asker.lock().chunk_count(),
        ChunkCount::from(0_usize),
        "the chunk that verified before it is not kept either"
    );
    assert_eq!(
        asker.fetch(&holder, &manifest, &[]),
        Err(Fault::Malformed { peer: holder.id() }),
        "a part shorter than a digest does not frame"
    );
    assert_eq!(at_asker.lock().chunk_count(), ChunkCount::from(0_usize));
    serving.join().expect("the forged holder ends");
}

#[test]
fn a_value_the_holder_lacks_is_refused_by_its_first_chunk()
{
    let holder = on_loopback(&Chunks::new());
    let at_asker = Chunks::new();
    let mut asker = on_loopback(&at_asker);
    let mut values = Store::new();
    let original = list(&mut values, Edited::No);
    let elsewhere =
        commit(&values, original, params(), &mut InMemoryChunkStore::new()).expect("crosses");
    assert_eq!(
        asker.fetch(&peer_of(&holder), &elsewhere, &[]),
        Err(Fault::Refused {
            peer: holder.node_id(),
            refusal: ValueError::UnknownChunk {
                digest: elsewhere.root().digest()
            },
        }),
        "a holder lacking the value answers nothing, and the walk names its root chunk"
    );
    assert_eq!(at_asker.lock().chunk_count(), ChunkCount::from(0_usize));
}
