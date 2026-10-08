# gandr-storage-records

The **authenticated ordered-record plane**: a content-defined Merkle search tree over sorted byte records, with proofs that a key is present, that a key is absent, or that a range holds exactly these records — each checkable against a root alone, with no access to the store the tree was built into.

One artifact is a set of records under an ordering key. Two versions of such an artifact usually differ in a few records, and the storage tier wants three things from that: the unchanged parts shared rather than rewritten, the whole carrying one name, and a part provable against that name without shipping the whole. A tree whose leaves end where the data says gives all three, because an edit perturbs the leaf it falls in and leaves its neighbours identical — keeping their identities, and so their storage.

## Status

Ported from the `storage-prolly-trees` crate of the pre-reboot prototype and revised against the reboot constraints. The prototype was itself a source absorption of the owner's unpublished `prolly-bao` crate (Apache-2.0, same owner); the Prolly / Merkle-search-tree lineage is recorded under
[Ideas and references](#ideas-and-references).

The revisions, all constraint-driven:

- **Domain-separated digests, and a store that admits one byte language.** Every digest puts its domain string inside the hashed preimage: node, root manifest, record encoding, and boundary decision are four domains that cannot be confused for one another. The store trait admits node material and refuses everything else, which makes it the keyed plane's store rather than a general blob store. The reasoning is under [Two planes, one backing store](#two-planes-one-backing-store); it corrects a design the prototype carried, in which the two planes were to share one verified block store.
- **A total decode budget, not only per-structure ceilings.** The prototype bounded each declared count against the bytes that had to carry it, which bounds one node. Node count and per-node record count are separately bounded and their product is not, so a proof of many cheap nodes each near its own ceiling forces work proportional to that product. A saturating accumulator now bounds the total over one proof, beside the per-structure ceilings on node size, leaf records, children and carried nodes.
- **One proof shape per proof kind, checked positionally.** The prototype accepted both a compact and a full-tree layout for absence and range proofs, and located nodes by searching the carried list for a wanted identity. Each kind now admits exactly one layout and reads each node from the position it must occupy, so there is one verifier path per kind and no second path to disagree with the first — and no search.
- **A prover and a verifier that share their rules.** Child selection, the successor-leaf requirement, the bracketing-neighbour derivation and the selected leaf run are each one function called from both sides. Two implementations of one rule agree until they do not, and here a disagreement would read as a forgery.
- **Agreement is separated from root identity.** `TreeRoot` equality is identity of the commitment. Whether two trees hold the same records is a different question with its own answer, `RecordTree::agrees_with`, in which the digest is a fast path for _disagreement_ and an equal-root pair is handed to the deciding comparison over the records themselves. Reading an equal digest as agreement is a silent false agreement, which is the one error this comparison must not make.
- **The tree keeps its own structure.** The prototype re-decoded its own encoded root to answer a query or build a proof. The tree now holds its child references and leaf runs, so proving reads no bytes back.
- **Typed errors with no dependency.** `thiserror` is replaced by hand-written `Display` and `core::error::Error` implementations, and error payloads are typed (`RecordIndex`, `NodeHash`, `FailureContext`, `WireVersion`) rather than bare integers and strings. The crate is `no_std` over `core` and `alloc`, with BLAKE3 its only dependency.
- **No bare primitives across the crate's own signatures**, `#[repr(transparent)]` on every single-field wrapper, checked arithmetic throughout, no `as` conversions, and no `unwrap`/`expect`/`panic` outside tests.

Everything already conformant in the prototype — no recursion, flat id-addressed nodes with no owning pointer routed through a recursive type, fail-closed record discipline, canonical encodings with trailing bytes refused — is preserved. The tree is two levels deep and every structure and proof here is written for that and refuses any other shape; depth is named work rather than a partial implementation.

## Not ported

Three prototype surfaces are deliberately absent, each because it answers to something this repository does not have yet. None is a limitation of the tree.

- **The witness transcript encoding.** A wire format for shipping a proof belongs with a transport, and the storage tier's transport plane is unbuilt here. A proof is a value; encoding it is the transport's decision, and pinning a format before the transport exists fixes the wrong thing.
- **The snapshot byte stream and its verifier.** A whole-tree materialization format, kept in the prototype as adapter evidence against an external verified-streaming implementation. There is no adapter here to be evidence for.
- **The packed-segment store.** An in-memory prototype of an on-disk layout, carrying an alignment obligation owed to a zero-copy reader that does not exist. The store trait is the boundary a persistent implementation joins at.

## Two planes, one backing store

The storage tier has two planes with two grains, and this crate is one of them.

| plane | holds | cut between | this crate |
| ----- | ----- | ----------- | ---------- |
| **keyed records** | artifacts as record sets under an ordering key | records | yes |
| **single values** | one large value: a description, a machine state, a checkpointed environment | the value's own constructors | no |

The two are expected to share a backing object, and they cannot share a verifier. A value-plane chunk is not node material, and wrapping a chunk as a one-record leaf to fit it through this crate's store would make the chunk's identity a function of this crate's leaf framing rather than of the value's own canonical bytes — destroying exactly the identity the value plane exists to provide. Two byte languages in one backing namespace need domain-separated digests: the value plane's store is a **sibling trait** with the chunk domain inside its own hashed preimage, and one backing object implementing both traits delivers the shared store without a verifier that answers for material it cannot check.

## The boundary discipline, and where this crate sits in it

The storage tier's theory is the LoCalMem boundary discipline: one type-directed measure governing where sharing points, chunk points and duplication bounds live. Its programme is eight rungs. This crate is the **keyed plane's implementation**, which the programme leaves structurally unchanged under the adoption — the discipline's own related work draws the same line, applying content-defined cuts between the _keys_ of a sorted record store on one side and between the _constructors_ of a typed value on the other. One discipline, two grains, and gandr has both workloads.

What the rungs are, and what each needs that this repository does not have yet:

| rung | content | bearing on this crate |
| ---- | ------- | --------------------- |
| 0 | classify the wire vocabulary: boundary/alias verdicts and token bounds | none directly; it classifies kernel term tags |
| 1 | the metatheory port of the token model through the linearization bound | supplies the statements this crate's canonicality is checked against |
| 2 | a typed content-defined chunking profile beside the record-safe one | a sibling crate; the record-safe rule here is its degenerate instance, whose boundary vocabulary has one member |
| 3 | the value-plane chunk DAG, content pointers, commit and dereference | the other plane; shares the backing store, not the verifier |
| 4 | session checkpoints keyed by content pointers | consumes rung 3, not this crate |
| 5 | certificate transport addresses as content pointers | would supply the transport a proof encoding belongs to |
| 6 | the runtime design pass: the memory model as the value-representation specification | none directly |
| 7 | worlds and distribution alignment | none directly |

Rungs 0 through 3 landed in the prototype. **Rungs 4 through 7 are open**, and none of the four is a prerequisite for this crate: it is landable, and landed, on its own.

Two fences bind this crate and do not move. Every adopted statement is a deep-equality statement — integrity only, and a digest match licenses no rewrite, no admission and no replay skip. And a digest is a positive fast path only: different digests prove disagreement, equal digests hand off to the deciding comparison, and a structure keyed by digest validates its hit against content rather than answering from the key.

## The contract attributes

The `# Specification` prose stays the statement of record, and a combined `#[spec(...)]` attribute states the same predicate wherever one is a runtime-checkable expression. Fifty-eight of the crate's seventy-nine blocks carry one; the remaining twenty-one stay prose and name their boundary in `- provides:`.

A clause carries the whole of one `- requires:` or `- ensures:` line, never a decidable half of it. Three shapes recur:

- **refusal boundaries** — `RecordIndex::next`, `RecordCount::plus`, `KeyRange::new`, `TreeParams::ensure_supported`, `EncodingVersion::from_number`, `BoundaryMaskBits::try_from`, `BoundaryRecordCap::try_from`, and the two decode-work charges: each an `is_ok()` equivalence against the condition the body branches on, which is what stops a crafted node wrapping a total into agreement with its header;
- **independent references** — `find_record` against a linear scan, `select_in_range` against an unfiltered one, `RecordTree::agrees_with` against the direct record comparison, `encode_leaf` and `encode_internal` against the decoder, `inspect_node` against the materializing decoder, and each cursor read against the little-endian writer;
- **derived answers** — `leaf_spans` states the partition law over the spans it returns, and each proof builder states that the proof it returns passes its own verifier, which puts the L1 evidence obligation where the evidence is produced.

A block stays prose for one of four reasons, each recorded in its own `- provides:` line: the line relates two calls (`digest`, `hash_node`, `encode_record`'s injectivity, `TreeRoot::seal`, `RecordTree::build`), it names a tree the call does not hold (the three verifiers), it ranges over a value the body consumes (`ensure_strictly_sorted`, `decode_leaf`, `decode_node`), or it belongs to a type rather than a function, whose `maintains` is not evaluated when a value is constructed and would therefore be inert.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Open work

- **Depth beyond two.** The record count one internal root can address is bounded by the child ceiling. Past it the root becomes a level of internal nodes over internal nodes, and the proof shapes change with it: a membership proof becomes a path rather than a pair. This is the keyed plane's half of the storage tier's multi-level question.
- **A store-backed reader.** `StoredRoot` attests that a root's own node is present and verifies, and nothing more: it does not walk children, so it does not attest that the tree below is present. A reader that answers queries from a store needs a traversal with its own budget, and a handle that answered from a partially present tree would be worse than one that refuses.
- **A committed second boundary profile.** `BoundaryProfile` is the door a second rule enters by; the typed profile of rung 2 is the expected one.
- **Compact witnesses.** A proof carries whole leaves. Sibling-path witnesses would be smaller and are a size question, not a soundness one.
- **The canonicality statement as a proved theorem.** That two writers agreeing on the parameters agree on the root is enforced by construction and exercised by differential; the metatheory port of rung 1 is where it becomes a theorem.

## Using it

Build from a strictly increasing record sequence, write the nodes to a store, and prove.

```rust
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::RecordValue;
use gandr_storage_records::TreeParams;

fn example() -> Result<(), RecordTreeError> {
    let records = [
        RecordRef::new(b"alpha", b"1"),
        RecordRef::new(b"beta", b"2"),
        RecordRef::new(b"gamma", b"3"),
    ];
    let tree = RecordTree::build(records.as_slice(), TreeParams::current())?;

    let mut store = InMemoryBlockStore::new();
    tree.write_to(&mut store)?;

    let key = RecordKey::from(b"beta");
    let proof = tree.prove_membership(key)?;
    proof.verify(&tree.root(), key, RecordValue::from(b"2"))?;

    Ok(())
}
```

A verifier needs the root and the proof. It does not need the store, the tree, or the other records.

## Ideas and references

The named ideas: content-defined chunking as a cut rule that travels with the data; Merkle search trees as a history-independent authenticated ordered map; authenticated data structures and the proofs a root admits; domain separation of hash preimages; and the boundary discipline that supplies the storage tier's theory.

- Trevor Rainey, Nathan Borkowski, Michael Vollmer, Chaitanya Koparkar, Nathan Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. `doi:10.1145/3828688`; mechanization artifact `doi:10.5281/zenodo.20315616` — the boundary discipline the storage tier's programme adopts, and the source of the keyed/value plane split this crate is one side of.
- Alex Auvolat and François Taïani. "Merkle Search Trees: Efficient State-Based CRDTs in Open Networks." In _38th IEEE International Symposium on Reliable Distributed Systems (SRDS)_, 2019. Preprint `arXiv:1908.05808` — the ordered-record Merkle tree whose leaf boundaries are a function of content rather than of insertion order, which is the structure this crate builds.
- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." In _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001 — the content-defined cut rule, in the form this crate's degenerate one-boundary-type instance specializes.
- Michael Vollmer, Chaitanya Koparkar, Mike Rainey, Laith Sakka, Milind Kulkarni, and Ryan R. Newton. "LoCal: A Language for Programs Operating on Serialized Data." In _Proceedings of the 40th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2019)_, 2019 — the location typing the boundary discipline builds on; read here as the reference for surface-level location typing, not as a compilation model to adopt.
- Andrew Miller, Michael Hicks, Jonathan Katz, and Elaine Shi. "Authenticated Data Structures, Generically." In _Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '14)_, pages 411–423,
  2014. `doi:10.1145/2535838.2535851` — the general construction this crate
  deliberately does not follow: it targets untrusted-server verification and pays a digest per node, where the grain here is the leaf and the runtime is trusted.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020. `https://github.com/BLAKE3-team/BLAKE3-specs` — the hash family node and root identities are drawn from.

## License

Apache-2.0 WITH LLVM-exception.
