# gandr-storage-schema

The record plane under the C-set discipline: a schema of objects, total arrows, attributes and path equations, and a store of stably keyed parts with kept inverses, checked against its equations on every edit and proved against one root.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Measurement](#measurement)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

## Synopsis

**What.** A `Schema` is a finite presentation of a category with attributes: objects are tables, arrows are total foreign keys between them, attributes are typed byte columns, and equations are pairs of arrow paths every store must agree on. It is a canonical value whose `SchemaIdentity` is BLAKE3 of its image. A `Store` holds each object's parts under stable keys, a column per arrow and attribute, and the inverse of each indexed column. It commits each table as one `gandr-storage-records` tree and names the whole store by one `StoreRoot`, against which it proves part membership, arrow and attribute values, and complete preimages.

**Why.** Indexes kept as hand-encoded key families leave their invariants to convention: nothing stops a delete from leaving a reference dangling, or two keys that should agree from disagreeing. Stated as a schema, every reference is a total arrow the store checks, every agreement is an equation the store checks, and a preimage is a lookup with a proof that it is complete.

**How.** Parts are keyed by a per-table monotone counter and deleted by clearing a bit in the table's live set, so nothing is ever renumbered and a key names one part for the store's whole life. An `Edit` collects mutations, refuses each dangling reference by name as it is made, and on `finish` checks completeness and then every equation whose value the edit could have changed, found by walking equation paths backward through the kept inverses; a refused or dropped edit rolls back. `Store::pull_back` migrates a store along a `SchemaMap` whose equations are checked once, on the map.

## References

- Evan Patterson, Owen Lynch and James Fairbanks. "Categorical Data Structures for Technical Computing." _Compositionality_ 4, 5 (2022). [doi:10.32408/compositionality-4-5](https://doi.org/10.32408/compositionality-4-5) — C-sets with attributes, their column representation with materialized inverses, and data migration.
- Kristopher Brown, Evan Patterson, Tyler Hanks and James Fairbanks. "Computational Category-Theoretic Rewriting." _ICGT 2022_, LNCS 13349. [arXiv:2111.03784](https://arxiv.org/abs/2111.03784) — §2.3: the dangling condition a deletion of a referenced part violates.
- David I. Spivak. "Functorial Data Migration." _Information and Computation_ 217 (2012). [arXiv:1009.1166](https://arxiv.org/abs/1009.1166) — schemas as finitely presented categories and the pull-back migration Δ.

## Provided features

- `Presentation` and `Schema`: validated, order-independent schemas with a canonical image, `Schema::decode` of exactly that image, and lookups that refuse an unknown name or ordinal by kind.
- `Store`: reads of liveness, arrow targets, attribute values and indexed preimages; `Edit` transactions and one-step `add_part`, `set_arrow`, `set_value` and `delete_part`, each refusing by name with a `Refusal`.
- `Store::commit` and `Store::open`: one record tree per table in any `BlockStore`, one `StoreManifest` binding the schema identity, the record plane's parameters and every table's counter and root; reopening refuses records that are not canonical, a dangling arrow and a broken equation.
- `Store::prove` and `Proof::verify`: a `Question` answered against a `StoreRoot` alone.
- `SchemaMap` and `Store::pull_back`: the Δ migration, keys and counters kept.
- `keyed`: a factory's dialogue, project and provenance indexes as one schema, with the equation that holds a naming's task to its move's.

## Expected features

Attribute values are canonical bytes the caller chooses; the store compares and indexes them as bytes. A store answers proofs for its last commit. Columns are dense by key, so memory follows each table's counter rather than its live count.

## Examples

Refuse the dangling reference, then prove a preimage:

```rust
use gandr_storage_records::{InMemoryBlockStore, TreeParams};
use gandr_storage_schema::{Answer, Indexing, Presentation, Question, Refusal, Row, Schema, Store};

let schema = Schema::present(
    &Presentation::new()
        .object("V")
        .object("E")
        .arrow("src", "E", "V", Indexing::Indexed)
        .arrow("tgt", "E", "V", Indexing::Indexed),
)?;
let mut store = Store::new(schema, TreeParams::default())?;
let (vertex, edge) = (store.schema().object("V")?, store.schema().object("E")?);
let (src, tgt) = (store.schema().arrow("src")?, store.schema().arrow("tgt")?);

let one = store.add_part(vertex, &Row::new())?;
let two = store.add_part(vertex, &Row::new())?;
let joined = store.add_part(edge, &Row::new().arrow(src, one).arrow(tgt, two))?;
assert!(matches!(store.delete_part(vertex, one), Err(Refusal::Referenced { .. })));

store.commit(&mut InMemoryBlockStore::new())?;
let question = Question::Preimage { arrow: src, target: one };
let proof = store.prove(&question)?;
let answer = proof.verify(store.root(), store.schema(), TreeParams::default(), &question)?;
assert_eq!(answer, Answer::Preimage(Box::from([joined])));
# Ok::<(), gandr_storage_schema::StoreError>(())
```

## Measurement

`cargo bench -p gandr-storage-schema` times a store of 6400 parts — a cycle of 3200 vertices and 3200 edges, both arrows indexed — as the mean of one million operations on one x86-64 desktop:

| Operation | ns |
| --------- | -: |
| indexed preimage lookup, borrowed | 29 |
| indexed preimage lookup, copied out | 31 |
| insert-and-remove round trip of an edge | 298 |
| insert-and-remove round trip of a mark, no equation | 330 |
| the same, with an equation checked on each insert | 467 |

## Where the detail lives

- [`src/lib.rs`](src/lib.rs): the discipline adopted, the key model chosen with its alternatives and reversal, the equation check and the limits.
- [`src/schema.rs`](src/schema.rs): the schema image. [`src/manifest.rs`](src/manifest.rs): the store manifest and root. [`src/store/layout.rs`](src/store/layout.rs): how a table lies on the record plane, and reopening.
- [`src/store/edit.rs`](src/store/edit.rs): edits and their refusals. [`src/store/prove.rs`](src/store/prove.rs): proofs. [`src/migrate.rs`](src/migrate.rs): schema maps and what the pull-back preserves. [`src/keyed.rs`](src/keyed.rs): the keyed-index schema.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
