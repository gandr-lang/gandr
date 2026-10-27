# gandr-runtime-net

The network a host holds for its `Net` interface: streams to peers named by their keys, over QUIC through iroh, and the chunk wire that fetches a committed value by content.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Net` is the network one run reaches: it binds an `Endpoint` on its first operation, dials a `Peer`, accepts a dialer, and sends, receives and closes the streams it minted. A peer is its key, the identity, with the socket addresses a dialer may try for it; a stream is a `StreamId` the endpoint minted, held by this host alone; a frame is a byte sequence at most `MAX_FRAME` long. An endpoint also serves the `Chunks` its host committed values into, and `Endpoint::fetch` asks a peer for the chunks of a value it lacks, naming the values it already holds. Every refusal is a `Fault` that names what it refused.

**Why.** The `Net` interface of the core's host signature needs a driver behind it, so that two gandr processes exchange frames: the first step from one process to coordination, migration and distributed execution between hosts. Keys rather than addresses name peers, so a stream is bound to the peer its dialer named wherever that peer is reached. A value moves between hosts by content, committed at one end and read back at the other, so the second end needs the chunks it lacks, and an edited value should cost only the chunks the edit changed.

**How.** The endpoint is an iroh endpoint under the `gandr/net/0` ALPN, with the relay off and the minimal preset, on a thread of its own running a current-thread tokio runtime; the program's thread asks it one operation at a time over a channel and waits for the answer. A task beside the requests accepts every connection: a dialer's stream waits for the owner's `accept`, and a fetch under `gandr/chunks/0` is answered at once. Each stream is one QUIC connection carrying one bidirectional stream, each frame a little-endian 32-bit length and its bytes. A close finishes this end, drains the peer's end to its finish, waits until the peer acknowledged every byte, then closes the connection, so neither end loses data the other sent. A fetch is one request, the wanted value's manifest and those of the values held, answered by every chunk of the wanted closure outside the held closures; the asker verifies each chunk against its digest before it keeps any, then walks the closure. Lookup is explicit, the addresses a peer carries, or mDNS on the local network.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — lineage: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — a stream is a location its host holds and never moves, beside the content-addressed values that do cross.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage programme's worlds and sessions; the chunk wire carries a migrating value's chunks to its destination.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: verdict reuse; a fetched chunk is checked for integrity alone.
- [`iroh`](https://docs.rs/iroh/1.3.0/iroh/): the endpoint, its keys and its QUIC connections.

## Provided features

- `Net`: the network one run reaches, bound on its first operation.
- `Endpoint`, `Binding`, `Lookup`, `ALPN`: a bound endpoint, what it binds with and how it finds a peer.
- `Peer`, `NodeId`, `Secret`, `PeerError`: a peer's key and addresses spelled `<key>@<ip:port>…`, the key alone, the secret an endpoint proves its key with, and why a spelling was refused.
- `StreamId`, `MAX_FRAME`, `Fault`: a stream, the largest frame, and every refusal an operation makes.
- `Chunks`, `CHUNKS_ALPN`, `Fetched`: the store an endpoint serves and fetches into, shared with its host; the fetch protocol's name; what one fetch carried.

## Expected features

- **UDP sockets.** A binding names the sockets it holds; with none, the endpoint binds every interface on a port the system picks.
- **A dialer that knows the peer's key.** A peer's key is its identity; a dial without an address finds the peer only under mDNS lookup.

## Examples

The tests bind two endpoints on loopback and exchange frames through them, refuse a held socket, an oversized frame and an unknown stream, and bind a network on its first operation. The chunk tests fetch a list and then an edit of it, counting the second fetch against the chunks the edit added and the locality bound, and refuse a forged holder's tampered chunk, an unframed answer and a value the holder lacks.

```sh
cargo test -p gandr-runtime-net
```

## Where the detail lives

`src/lib.rs` states the crate's place among the stores; `src/endpoint.rs` the operations, the frame and every fault; `src/endpoint/driver.rs` the endpoint's thread, the streams it holds, the accepting task and the close; `src/chunks.rs` the chunk wire, its framing and its boundaries; `src/peer.rs` keys and their spelling; `src/net.rs` the lazy binding.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
