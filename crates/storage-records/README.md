# gandr-storage-records

An authenticated ordered-record plane with content-defined Merkle leaves and root-checkable membership, absence and range proofs.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Tree and proof shapes](#tree-and-proof-shapes)
- [Decode budgets](#decode-budgets)
- [Identity and agreement](#identity-and-agreement)
- [Storage planes](#storage-planes)
- [Specification attributes](#specification-attributes)
- [License](#license)

## Synopsis

**What.** `gandr-storage-records` builds an authenticated tree over strictly ordered byte records. A `TreeRoot` binds the tree's parameters, record count and root-node identity. Membership, non-membership and range proofs are checked against that root without access to the tree or its store.

**Why.** Versions of a record set often differ in only a few records. Content-defined leaf boundaries allow unchanged runs to retain their identities and storage, while one root names the whole set. Proofs let a consumer authenticate selected records or establish their absence without receiving the whole artifact.

**How.** Each record supplies one token and a domain-separated BLAKE3 residue to the typed scanner in `gandr-storage-chunker`. The scanner partitions the sorted sequence into leaves; an internal root commits their separators when there is more than one leaf. Canonical node encodings and domain-separated commitments give deterministic identities, while positional proof verification authenticates the requested records under explicit decode budgets.

## References

- Trevor Rainey, Nathan Borkowski, Michael Vollmer, Chaitanya Koparkar, Nathan Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688); [mechanization artifact, doi:10.5281/zenodo.20315616](https://doi.org/10.5281/zenodo.20315616) — the boundary discipline and distinction between keyed records and typed values.
- Alex Auvolat and François Taïani. "Merkle Search Trees: Efficient State-Based CRDTs in Open Networks." _38th IEEE International Symposium on Reliable Distributed Systems (SRDS)_, 2019. [arXiv:1908.05808](https://arxiv.org/abs/1908.05808) — content-dependent authenticated ordered structure independent of insertion order.
- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001. [doi:10.1145/502034.502052](https://doi.org/10.1145/502034.502052) — content-defined cuts, specialized here to whole records.
- Michael Vollmer, Chaitanya Koparkar, Mike Rainey, Laith Sakka, Milind Kulkarni, and Ryan R. Newton. "LoCal: A Language for Programs Operating on Serialized Data." _Proceedings of the 40th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2019)_, 2019. [doi:10.1145/3314221.3314631](https://doi.org/10.1145/3314221.3314631) — location typing underlying the boundary discipline.
- Andrew Miller, Michael Hicks, Jonathan Katz, and Elaine Shi. "Authenticated Data Structures, Generically." _Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '14)_, pages 411–423, 2014. [doi:10.1145/2535838.2535851](https://doi.org/10.1145/2535838.2535851) — root-checkable evidence as a comparison point for this crate's leaf-grained authentication.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs) — the hash family for node, root, record and boundary domains.

## Provided features

- `RecordTree` builds from strictly increasing keys and supports lookup, range selection and node export.
- Membership, non-membership and range proof builders produce evidence checked against a `TreeRoot` alone.
- Canonical node encoders and decoders reject malformed framing, unsupported parameters and trailing bytes.
- `BlockStore` defines verified node storage; `InMemoryBlockStore` supplies an in-memory implementation.
- `StoredRoot` verifies a root node's presence; `RecordTree::agrees_with` compares complete record sets.
- Typed `RecordTreeError` values distinguish ordering, authentication, shape and budget failures.

## Expected features

Callers supply canonical key and value bytes in strictly increasing key order. Duplicate or unsorted keys are errors; the builder does not sort or repair them. Writers sharing identities must agree on `TreeParams`.

Persistent storage implements `BlockStore` and verifies canonical node material on both insertion and load. Verifiers require a trusted expected root and the query being authenticated. The crate uses `core` and `alloc` under `no_std`, so consumers supply an allocator.

## Examples

Build a tree, write its nodes and verify a membership proof:

```rust
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::RecordValue;
use gandr_storage_records::TreeParams;

fn main() -> Result<(), RecordTreeError> {
    let records = [
        RecordRef::new(b"alpha", b"1"),
        RecordRef::new(b"beta", b"2"),
        RecordRef::new(b"gamma", b"3"),
    ];
    let tree = RecordTree::build(records.as_slice(), TreeParams::current())?;
    let mut store = InMemoryBlockStore::new();
    tree.write_to(&mut store)?;

    let root = tree.root();
    let key = RecordKey::from(b"beta");
    let proof = tree.prove_membership(key)?;
    proof.verify(&root, key, RecordValue::from(b"2"))?;
    Ok(())
}
```

The verification call uses neither the store nor the tree. Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-storage-records
```

## Tree and proof shapes

A tree is one leaf or one internal root over a run of leaves. Node encodings and proof shapes enforce this two-level limit; the child ceiling bounds the number of leaves a root can address. The tree retains its child references and leaf runs, so proving requires no decoding of its own nodes.

Each proof kind admits one layout, with carried nodes checked in their required positions. Prover and verifier share child selection, successor-leaf selection, bracketing and selected-run rules. Proofs carry whole leaves and are Rust values; transport framing belongs to the consumer.

`StoredRoot` attests only that the root node is present and verifies. It does not traverse children or establish that all leaves are available. Queries and proof construction use the in-memory `RecordTree`.

## Decode budgets

Verification bounds both individual structures and total work. Ceilings cover node bytes, leaf records, children and carried nodes; a saturating accumulator bounds work across one proof. Separate per-node limits alone would permit work proportional to their product with the node count. Exhaustion returns `RecordTreeError::BudgetExceeded`.

## Identity and agreement

`TreeRoot` equality compares commitments. `RecordTree::agrees_with` decides equality of the records themselves: with matching parameters, different root identities establish disagreement; equal identities still require the record comparison. Different parameter sets also require that comparison, because the same records can have different commitments.

A store or proof verifier recomputes each identity from the bytes it holds. Authentication establishes integrity under the supplied root, not application-level admissibility or permission to skip a deciding comparison.

## Storage planes

Record nodes and value chunks have separate byte languages and verification boundaries.

| Plane | Content | Cut positions | Store trait |
| ----- | ------- | ------------- | ----------- |
| `gandr-storage-records` | Sorted keyed records | Between records | `BlockStore` |
| `gandr-storage-values` | One typed value | Constructor exits | `ChunkStore` |

One backing object can implement both traits. Wrapping a value chunk as a record leaf would make its identity depend on leaf framing rather than the value's canonical bytes. Separate traits preserve each plane's admission rule, while domain strings inside hashed preimages separate their identities. Node, root-manifest, record-encoding and boundary-decision hashes each use a distinct domain; committed integers are fixed-width little-endian.

## Specification attributes

`# Specification` blocks state the admitted behavior. Executable `#[spec(...)]` predicates check refusal conditions, independent comparisons and derived results on executed calls. Statements relating separate calls or unavailable values remain prose obligations with their limits stated beside the implementation.

The enforcing test lane uses `--cfg anodized_panic` across the dependency graph. `anodized` uses core-only helpers with default features disabled.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
