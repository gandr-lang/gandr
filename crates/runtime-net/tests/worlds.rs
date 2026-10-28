//! The world wire on loopback: a far endpoint fetches a migration's captures
//! over the connection it came on and answers, the asker fetching the answer
//! the same way; a refusal crosses back with nothing fetched, and a
//! configuration that does not frame never reaches the far owner.

use core::net::IpAddr;
use core::net::Ipv4Addr;
use core::net::SocketAddr;
use core::str::FromStr as _;
use std::thread;

use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::Store;
use gandr_core_term::world::Unmigrated;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::crossing::commit;
use gandr_runtime_emitter::crossing::deref;
use gandr_runtime_net::Answer;
use gandr_runtime_net::Binding;
use gandr_runtime_net::Chunks;
use gandr_runtime_net::Code;
use gandr_runtime_net::Configuration;
use gandr_runtime_net::Endpoint;
use gandr_runtime_net::Fault;
use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;
use gandr_runtime_net::WORLDS_ALPN;
use gandr_runtime_net::WorldName;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ValueManifest;

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

/// The integer `value` allocated in `store`.
///
/// # Specification
/// trivial.
fn integer(
    store: &mut Store,
    value: Small,
) -> HeapValueId
{
    store
        .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::from_decimal_text(value.0.to_string()).expect("digits"),
        ))))
        .expect("room")
}

/// A small non-negative integer a witness spells.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Small(u8);

/// The pair of `fields`, in order, allocated in `store`.
///
/// # Specification
/// trivial.
fn pair(
    store: &mut Store,
    fields: [HeapValueId; 2],
) -> HeapValueId
{
    store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::from(2_usize)),
            fields: Box::new(fields),
        })
        .expect("room")
}

/// The manifest `value` of `store` commits to, written to a scratch store.
///
/// # Specification
/// trivial.
fn manifest_of(
    store: &Store,
    value: HeapValueId,
) -> ValueManifest
{
    commit(store, value, params(), &mut InMemoryChunkStore::new()).expect("the value crosses")
}

/// The migration a witness ships: the code `swap` to the world `seat`, over
/// `captures`.
///
/// # Specification
/// trivial.
fn swap(captures: Vec<ValueManifest>) -> Configuration
{
    Configuration::new(
        Code::from(b"swap".to_vec()),
        WorldName::from("seat"),
        captures,
    )
}

/// The asker commits 20 and 22 and ships them; the far owner reads the
/// asker's key and the configuration it sent, fetches both captures over the
/// connection, answers the pair `(22, 20)`, and the asker reads that pair
/// back from its own store. An arrival answered once is unknown after.
#[test]
fn a_migration_runs_at_the_far_host_and_its_answer_comes_back()
{
    let (near_chunks, far_chunks) = (Chunks::new(), Chunks::new());
    let (mut near, mut far) = (on_loopback(&near_chunks), on_loopback(&far_chunks));
    let mut here = Store::new();
    let (twenty, twenty_two) = (integer(&mut here, Small(20)), integer(&mut here, Small(22)));
    let captures = {
        let mut chunks = near_chunks.lock();
        [twenty, twenty_two]
            .map(|value| commit(&here, value, params(), &mut *chunks).expect("an integer crosses"))
    };
    let configuration = swap(captures.to_vec());
    let swapped = pair(&mut here, [twenty_two, twenty]);
    let expected = manifest_of(&here, swapped);
    let (asker, far_peer) = (near.node_id(), peer_of(&far));
    let sent = configuration.clone();
    let serving = thread::spawn(move || {
        let arrival = far.arrive().expect("the migration arrives");
        assert_eq!(
            (arrival.from, &arrival.configuration),
            (asker, &sent),
            "the far owner reads the asker's key and its configuration"
        );
        let mut there = Store::new();
        let fetched = sent
            .captures()
            .iter()
            .map(|capture| {
                far.fetch_arrived(arrival.id, capture, &[])
                    .expect("a capture is fetched over the migration's connection");
                deref(capture, params(), &*far_chunks.lock(), &mut there)
                    .expect("a fetched capture reads back")
            })
            .collect::<Vec<HeapValueId>>();
        let [first, second]: [HeapValueId; 2] = fetched.try_into().expect("two captures");
        let answered = pair(&mut there, [second, first]);
        let manifest =
            commit(&there, answered, params(), &mut *far_chunks.lock()).expect("the pair crosses");
        far.answer(arrival.id, &Answer::Answered(manifest))
            .expect("the answer is sent");
        let again = far.answer(arrival.id, &Answer::Answered(manifest));
        (far, again)
    });
    let answer = near
        .migrate(&far_peer, &configuration)
        .expect("the migration completes");
    let (far, again) = serving.join().expect("the far owner answers");
    assert_eq!(
        (answer, again),
        (
            Answer::Answered(expected),
            Err(Fault::Unarrived(gandr_runtime_net::ArrivalId::from(0_u64)))
        ),
        "the answer is the pair's manifest, and an answered arrival is unknown"
    );
    let mut back = Store::new();
    let read = deref(&expected, params(), &*near_chunks.lock(), &mut back)
        .expect("the answer's chunks are in the asker's store");
    assert_eq!(
        manifest_of(&back, read),
        expected,
        "the answer reads back from the asker's own store"
    );
    drop(far);
}

/// A far owner that runs nothing refuses without fetching, by each reason in
/// turn: every refusal crosses back as itself, the far store stays empty,
/// and the asker's holds only its capture.
#[test]
fn a_refusal_crosses_back_and_nothing_is_fetched()
{
    const REASONS: [Unmigrated; 6] = [
        Unmigrated::UnboundWorld,
        Unmigrated::Unreached,
        Unmigrated::Unheld,
        Unmigrated::Unserved,
        Unmigrated::Unfetched,
        Unmigrated::Unanswered,
    ];
    let (near_chunks, far_chunks) = (Chunks::new(), Chunks::new());
    let (mut near, mut far) = (on_loopback(&near_chunks), on_loopback(&far_chunks));
    let mut here = Store::new();
    let value = integer(&mut here, Small(21));
    let capture =
        commit(&here, value, params(), &mut *near_chunks.lock()).expect("an integer crosses");
    let far_peer = peer_of(&far);
    let serving = thread::spawn(move || {
        for reason in REASONS {
            let arrival = far.arrive().expect("the migration arrives");
            far.answer(arrival.id, &Answer::Refused(reason))
                .expect("the refusal is sent");
        }
        far
    });
    let answers: Vec<Answer> = REASONS
        .iter()
        .map(|_reason| {
            near.migrate(&far_peer, &swap(vec![capture]))
                .expect("the migration completes")
        })
        .collect();
    let far = serving.join().expect("the far owner refuses");
    assert_eq!(
        (
            answers,
            far_chunks.lock().chunk_count(),
            near_chunks.lock().chunk_count()
        ),
        (
            REASONS.map(Answer::Refused).to_vec(),
            ChunkCount::from(0_usize),
            ChunkCount::from(1_usize)
        ),
        "each refusal comes back as itself and no chunk moved"
    );
    drop(far);
}

/// A far owner dropped as soon as it answers still serves the answer's
/// chunks: the asker reads the answered pair back from its own store, as it
/// would from an owner that went on running.
#[test]
fn an_owner_dropped_once_it_answers_still_serves_the_answer()
{
    let (near_chunks, far_chunks) = (Chunks::new(), Chunks::new());
    let (mut near, mut far) = (on_loopback(&near_chunks), on_loopback(&far_chunks));
    let mut there = Store::new();
    let fields = [Small(6), Small(7)].map(|value| integer(&mut there, value));
    let answered = pair(&mut there, fields);
    let expected = manifest_of(&there, answered);
    let far_peer = peer_of(&far);
    let serving = thread::spawn(move || {
        let arrival = far.arrive().expect("the migration arrives");
        let manifest =
            commit(&there, answered, params(), &mut *far_chunks.lock()).expect("the pair crosses");
        far.answer(arrival.id, &Answer::Answered(manifest))
            .expect("the answer is sent");
        drop(far);
    });
    let answer = near.migrate(&far_peer, &swap(Vec::new()));
    serving.join().expect("the far owner answers and ends");
    assert_eq!(
        answer,
        Ok(Answer::Answered(expected)),
        "the answer crosses although its owner ended"
    );
    let mut back = Store::new();
    let read = deref(&expected, params(), &*near_chunks.lock(), &mut back)
        .expect("the answer's chunks are in the asker's store");
    assert_eq!(
        manifest_of(&back, read),
        expected,
        "the answer reads back from the asker's own store"
    );
}

/// A dialer that sends bytes the wire does not frame under [`WORLDS_ALPN`] is
/// closed unanswered, and the far owner's `arrive` answers the next
/// migration that frames.
#[test]
fn a_configuration_that_does_not_frame_is_never_offered()
{
    let (near_chunks, far_chunks) = (Chunks::new(), Chunks::new());
    let (mut near, mut far) = (on_loopback(&near_chunks), on_loopback(&far_chunks));
    let far_peer = peer_of(&far);
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("a runtime");
    let refused = runtime.block_on(async {
        let dialer = iroh::Endpoint::builder(iroh::endpoint::presets::Minimal)
            .alpns(Vec::from([WORLDS_ALPN.to_vec()]))
            .relay_mode(iroh::RelayMode::Disabled)
            .bind_addr(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
            .expect("a loopback socket")
            .bind()
            .await
            .expect("the dialer binds");
        let key = iroh::PublicKey::from_str(&far_peer.id().to_string()).expect("a key");
        let dialed = far_peer
            .addresses()
            .iter()
            .fold(iroh::EndpointAddr::new(key), |dialed, &address| {
                dialed.with_ip_addr(address)
            });
        let connection = dialer
            .connect(dialed, WORLDS_ALPN)
            .await
            .expect("the handshake completes");
        let (mut send, mut recv) = connection.open_bi().await.expect("a stream");
        send.write_all(&[0xff, 0xff, 0xff, 0xff, 1])
            .await
            .expect("the bytes are written");
        send.finish().expect("the bytes end");
        let read = recv.read_to_end(64).await;
        dialer.close().await;
        read.is_err()
    });
    let asker = near.node_id();
    let serving = thread::spawn(move || {
        let arrival = far.arrive().expect("a migration arrives");
        far.answer(arrival.id, &Answer::Refused(Unmigrated::Unheld))
            .expect("the refusal is sent");
        (far, arrival.from)
    });
    let answer = near
        .migrate(&far_peer, &swap(Vec::new()))
        .expect("the migration completes");
    let (far, from) = serving.join().expect("the far owner answers");
    assert_eq!(
        (refused, from, answer),
        (true, asker, Answer::Refused(Unmigrated::Unheld)),
        "the unframed dialer is closed, and the first arrival is the asker's"
    );
    drop(far);
}
