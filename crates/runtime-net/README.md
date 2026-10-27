# gandr-runtime-net

The network a host holds for its `Net` interface: streams to peers named by their keys, over QUIC through iroh.

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

**What.** A `Net` is the network one run reaches: it binds an `Endpoint` on its first operation, dials a `Peer`, accepts a dialer, and sends, receives and closes the streams it minted. A peer is its key, the identity, with the socket addresses a dialer may try for it; a stream is a `StreamId` the endpoint minted, held by this host alone; a frame is a byte sequence at most `MAX_FRAME` long. Every refusal is a `Fault` that names what it refused.

**Why.** The `Net` interface of the core's host signature needs a driver behind it, so that two gandr processes exchange frames: the first step from one process to coordination, migration and distributed execution between hosts. Keys rather than addresses name peers, so a stream is bound to the peer its dialer named wherever that peer is reached.

**How.** The endpoint is an iroh endpoint under the `gandr/net/0` ALPN, with the relay off and the minimal preset, on a thread of its own running a current-thread tokio runtime; the program's thread asks it one operation at a time over a channel and waits for the answer. Each stream is one QUIC connection carrying one bidirectional stream, each frame a little-endian 32-bit length and its bytes. A close finishes this end, drains the peer's end to its finish, waits until the peer acknowledged every byte, then closes the connection, so neither end loses data the other sent. Lookup is explicit, the addresses a peer carries, or mDNS on the local network.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — lineage: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — a stream is a location its host holds and never moves, beside the content-addressed values that do cross.
- [`iroh`](https://docs.rs/iroh/1.3.0/iroh/): the endpoint, its keys and its QUIC connections.

## Provided features

- `Net`: the network one run reaches, bound on its first operation.
- `Endpoint`, `Binding`, `Lookup`, `ALPN`: a bound endpoint, what it binds with and how it finds a peer.
- `Peer`, `NodeId`, `Secret`, `PeerError`: a peer's key and addresses spelled `<key>@<ip:port>…`, the key alone, the secret an endpoint proves its key with, and why a spelling was refused.
- `StreamId`, `MAX_FRAME`, `Fault`: a stream, the largest frame, and every refusal an operation makes.

## Expected features

- **UDP sockets.** A binding names the sockets it holds; with none, the endpoint binds every interface on a port the system picks.
- **A dialer that knows the peer's key.** A peer's key is its identity; a dial without an address finds the peer only under mDNS lookup.

## Examples

The tests bind two endpoints on loopback and exchange frames through them, refuse a held socket, an oversized frame and an unknown stream, and bind a network on its first operation.

```sh
cargo test -p gandr-runtime-net
```

## Where the detail lives

`src/lib.rs` states the crate's place among the stores; `src/endpoint.rs` the operations, the frame and every fault; `src/endpoint/driver.rs` the endpoint's thread, the streams it holds and the close; `src/peer.rs` keys and their spelling; `src/net.rs` the lazy binding.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
