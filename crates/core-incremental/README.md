# gandr-core-incremental

Incremental checking over the core judgement: each revision's typings equal a batch run's, and only the items whose earlier answer no longer holds are judged again.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The incremental contract](#the-incremental-contract)
- [Identity: references, content, handles](#identity-references-content-handles)
- [Validated resume](#validated-resume)
- [Checkpoints and their stores](#checkpoints-and-their-stores)
- [The synthesis stream](#the-synthesis-stream)
- [Redesigned rather than ported](#redesigned-rather-than-ported)
- [Tests: the floor, the held rows, the defects](#tests-the-floor-the-held-rows-the-defects)
- [Consumer and open rows](#consumer-and-open-rows)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A front end hands over one `Program` per revision: `Item`s, each a front-end `ItemKey` beside the checker's own `Declaration`, over one `CoreArena`. `check_program` judges every item; `resume` takes the previous revision's `Resume` and answers the edited program, adopting each item's checkpoint only when it still answers and judging the rest. Checkpoints persist under their program's content address in a memory or an atomic file store, and a `SynthesisStream` publishes each item's handle, typing and adoption, then the match liveness its producer computed.

**Why.** A checker that answers an editor on every keystroke cannot judge the whole program each time, and a checker that reuses answers it cannot justify answers wrongly. This crate reuses only what the judgement itself says it depended on, compared value by value, so reuse is a saving and never a change of answer: incremental equals batch, and the tests hold it to that over generated programs and edit chains.

**How.** Batch and incremental are one forward pass at two memos. Each item is encoded once into id-free content; the memo recalls a base checkpoint of equal content; the checkpoint is adopted when every signature answer its judgement consulted equals the edited table's answer at that point of the pass, no type position of it reads a definition whose value changed, and its type can be seated in the edited arena. A value change closes over readers once, through reverse read edges. Item identity across revisions rides on an order-maintenance structure from `gandr-theory-orders`.

## References

- Thomas J. Porter, Marisa Kirisame, Ivan Wei, Pavel Panchekha, and Cyrus Omar. "Incremental Bidirectional Typing via Order Maintenance." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025), pages 1865–1892. `doi:10.1145/3763117`; preprint `arXiv:2504.08946` — incremental typing over an order-maintenance structure, the setting this crate's item order serves.
- Paul F. Dietz and Daniel D. Sleator. "Two Algorithms for Maintaining Order in a List." In _Proceedings of the Nineteenth Annual ACM Symposium on Theory of Computing (STOC '87)_, pages 365–372, 1987. `doi:10.1145/28395.28434` — the order-maintenance problem the handles live in.
- Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones. "Build Systems à la Carte." _Proceedings of the ACM on Programming Languages_ 2, ICFP (2018), Article 79. `doi:10.1145/3236774` — verifying traces: a result is reused when the recorded values of what it read still match, which is what a checkpoint's support is.
- Michael L. Fredman. "On Computing the Length of Longest Increasing Subsequences." _Discrete Mathematics_ 11, 1 (1975), pages 29–35. `doi:10.1016/0012-365X(75)90103-X` — the patience-sorting bound the handle splice runs in.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." 2020. <https://github.com/BLAKE3-team/BLAKE3-specs> — the digest behind memo identities and content addresses.

## Provided features

- **The item seam.** `Program`, `Item`, `ItemKey`, `Reference`, `ItemSource`: items keyed by the front end, admission positions checked once (`ProgramError`), and every position read as the `Reference` — key and occurrence — it resolves to.
- **Content.** `ItemContent`, `TypeContent`, `ContentNode`, `Opacity`: an item's or a type's nodes as one table numbered by discovery, free of arena ids; `TypeContent::of_value_type` reads a type, and a table holding an id its arena does not resolve is opaque.
- **The conservative footprint.** `footprint_of` and `Footprint`: every reference an item mentions, those in type positions apart, its opacity and whether its body is a hole.
- **Validated resume.** `check_program`, `resume`, `resume_from`, `Resume`, `Checkpoints`, `ItemCheckpoint`, `Answered`, `Answer`, `Adoption`, `ResumeCensus`, and `project`, which turns a verdict of the checker's own batch entry into the `Typing` this crate records, so a caller can compare the two.
- **Item identity.** `ItemHandle` and `Resume::compare`: a handle per item that survives edits elsewhere and compares in constant time.
- **Checkpoints and stores.** `encode_checkpoints`, `decode_checkpoints`, `CheckpointBytes`, `UnsupportedPersistence`, `address_of`, `persist`, `restore`, `CheckpointStore`, `MemoryCheckpointStore`, `FileCheckpointStore`, `CheckpointObserver`, `BackendArtifact`, `CheckpointAddress`, `CheckpointStoreError`.
- **The session.** `IncrementalSession` and `SessionError`: one call per revision that resumes, persists and keeps the latest resume for streaming.
- **The synthesis stream.** `SynthesisStream`, `SynthesisEvent`, `Liveness`, `MatchOrigin`, `BranchStatus`.

## Expected features

- **A hosted target.** The file store reads and writes the file system through `std`; every other module uses `core` and `alloc` alone.
- **The checker's support entry.** `gandr_core_checker::check_declaration_supported` judges one declaration and reports the signature answers it consulted; `CheckingContext::adopt` admits an answer as if judged. The crate is built on those two and on nothing private to the checker.
- **`--cfg anodized_panic` for enforcement.** The enforcing test lane builds the dependency graph with it, so every checked specification clause panics on a violation.

## Examples

Judge a program, edit one definition's value, and resume:

```rust
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Program;
use gandr_core_incremental::check_program;
use gandr_core_incremental::resume;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use quenchant_shape::shape::Maybe;

// def a = <digits> ; def b = a
let program = |digits: &str| {
    let mut arena = CoreArena::new();
    let literal = arena.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(digits.into()).expect("decimal digits"),
    )));
    let a = arena.value_constant(ConstantIndex::from(0_usize));
    let item = |key: &str, position: usize, body| {
        Item::new(
            ItemKey::from(key),
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(body),
                OriginToken::from(position),
            ),
        )
    };
    Program::new(arena, vec![item("a", 0, literal), item("b", 1, a)]).expect("ascending")
};

let base = check_program(&mut program("0"), CheckBudget::DEFAULT).expect("order");
let edited = resume(base, &mut program("1")).expect("order");
// a's value changed and its type did not: b's recorded answer for a still holds.
assert_eq!(edited.adoptions(), [Adoption::Judged, Adoption::Adopted]);
```

Run the tests, then the enforcing twin:

```sh
cargo nextest run -p gandr-core-incremental
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-core-incremental
```

## The incremental contract

**Support is an output of the judgement.** The checker reports, for each declaration it judges, every signature answer it consulted: the reference asked about and the answer given, the type's content or none. That list is the item's support, and a checkpoint stores it. Reuse is licensed by comparing it, entry by entry, against the answers the edited program's table gives at the same point of the pass. Nothing else licenses reuse: not a footprint, not a name, not an edit's location. A footprint over-approximates what an item could read; the support is what it did read, which is both tighter and exact.

**The entry answers one item.** The checker's per-declaration entry judges one declaration against the table the items before it built, so the pass interleaves judging and adopting in source order, and an adopted item enters the table exactly as a judged one would (`CheckingContext::adopt`). The answers an item supplies are derived, never stored: a signed item supplies its signature when it forms, an unsigned item the type it synthesised, and both are re-derived from the edited program at adoption.

**Incremental equals batch.** `check_program` is the pass at a memo that recalls nothing; `resume` is the same pass at a memo that recalls base checkpoints. The differential suite holds the resume equal to the checker's module entry — the batch pipeline the surface dispatcher runs — projected through `project`, on every named edit and every generated program and edit chain. It is the primary assertion; every other test is secondary to it.

**One memo, two machines.** Recall goes through `gandr-kernel-check-memo`'s `OrderedMemo`, the memo the checking kernel uses: an item's identity is its content, bucketed by the first sixteen bytes of the content's BLAKE3 digest and confirmed by content equality, so a digest collision costs a comparison and never a wrong recall.

## Identity: references, content, handles

**References, not positions.** An admission position is an artefact of one revision. Every position an item mentions is read as the `Reference` it resolves to — the key of the item at that position and how many items of that key precede it — or `Unoccupied`. Two revisions agree on what an item reads exactly when they agree on references.

**Content, not ids.** An item's content is its reference and every node reachable from its signature and its body, numbered in the order a breadth-first walk from the two roots discovers them. The walk visits each node once and needs no stack. Sharing is part of the content: two graphs with different sharing differ, which costs a reuse and never a wrong answer. An id its arena does not resolve is listed by sort, and the item is opaque: never recalled, never persisted, and a reader of everything once anything changed.

**Handles, not indices.** Each item holds a handle into an order-maintenance structure whose order is source order. A revision splices it: a longest run of surviving items whose base order the edit preserved keeps its handles (patience sorting, so a move costs the moved item's handle alone), every other item takes a fresh handle after its predecessor, and the rest are removed. Handles are identity for consumers — an editor's cursor, a stream reader's bookmark — and never evidence for the checker: reuse is decided by content.

| Decision | Alternatives | Reversal |
| -------- | ------------ | -------- |
| Identity by content, recalled through the shared memo | positional identity; identity by name | the front end supplies stable item ids that survive every edit |
| Keep handles on a longest preserved run | greedy keep-in-order, which loses every handle after a move to the front; a longest common subsequence over contents, quadratic | a consumer needs handles to follow moved items, which needs move detection in the front end |

## Validated resume

A recalled checkpoint is adopted when four things hold, checked in this order; the first that fails names the reason (`recall::Absent`):

1. The item is transparent.
2. Every recorded answer equals the edited table's answer for the same reference at this point of the pass: the answer the item of that reference supplied when it precedes this one, none otherwise.
3. No reference in a type position of the item, nor in the type of any recorded answer, names a definition in the value-changed set.
4. The adopted type seats: a signed item's signature forms in the edited context; an unsigned item's synthesised type is minted into the edited arena before the pass and forms.

**The value-changed set.** A definition inserted, deleted, or whose content differs between the revisions seeds the set; the set closes over the read relation of the edited footprints through reverse edges and a worklist, so every edge is crossed at most once. Once the set is non-empty every opaque item joins it. The closure guards answers that depend on a definition's _value_ while the support compares types: today's checker admits no type former that reads a term — `El` and abstract types are outside its fragment — so the guard declines items whose answer would not in fact change; it is kept so that admitting such a former cannot make reuse unsound. When the checker records value consults in the support, the closure can retire.

**Linear by construction.** Each item is encoded once, recalled at most once, adopted or judged once; the closure crosses each read edge at most once; the splice is one map build and one patience walk. `ResumeCensus` counts each of these, and a test pins the counts for a head edit of chains from 250 to 2,000 items.

| Decision | Alternatives | Reversal |
| -------- | ------------ | -------- |
| Pointwise support recorded by the judgement | compare bindings by name; compare footprints; re-judge every reader of an edited item | none: this is the soundness argument |
| Mint an unsigned item's synthesised type into the edited arena before the pass | judge every unsigned item a recalled reader depends on | minting dominates a measured profile |
| Close value changes over footprint reads, blocking type-position reads | no closure, since today's fragment consults no values | the checker records value consults in the support |
| Supplied answers derived at adoption | stored in the checkpoint | never: a stored answer would be trusted, not validated |

## Checkpoints and their stores

**One canonical encoding.** A checkpoint set encodes to one byte string: magic, allowance, then each item's content, footprint, support and typing, with sets ascending and tables in discovery order. Decoding refuses truncated, malformed and trailing bytes, a level atom whose offset reaches 4,096 (each step of the offset is a successor the decoder builds, so the cap bounds its work), and any payload that parses but is not the canonical spelling of its value — the decoded set is re-encoded and compared. An opaque item has no spelling, and encoding names the sort of its first unresolved id (`UnsupportedPersistence::Dangling`).

**Addressed by program, keyed by backend.** A set is stored under the BLAKE3 digest of its program's canonical bytes and the identity of the backend artifact that judged it, so it is only restored for the same program and the same checker. A restored set is validated by the next resume like any other.

**A failed store leaves the store as it was.** Both stores encode completely before they change anything. The file store writes the record — header with magic, version, address, backend, length and payload digest, then the payload — to a temporary it created exclusively under a fresh random name, publishes it with one rename, and removes the temporary on every other exit; it never opens a file it did not create. Loading checks the header, the address, the length and the digest before decoding. The store is atomic, not durable: it does not synchronise to the device.

| Decision | Alternatives | Reversal |
| -------- | ------------ | -------- |
| A crate-local canonical binary encoding with a canonicality check | a serialisation framework, which would add a dependency and admit several spellings of one value | the storage tier hosts session checkpoints (below) |
| BLAKE3 through the workspace `blake3` entry, the digest the storage tier uses | the storage tier's digest wrapper, which a `core` crate cannot depend on under the layering; a second hash function | the digest moves to a layer below both |
| Exclusive temporary, then rename | write in place; a fixed temporary name, which a squatter or a concurrent store could hijack | a consumer needs durability, which adds a sync before and after the rename |

## The synthesis stream

A stream opens with the item count, carries one event per item in source order — its handle, typing and adoption — then the match liveness its producer computed, by origin, and closes. Liveness follows the items because a match is addressed by source coordinates and one source item may lower to several core items. A submission whose source records are gone is named by an event of its own, because silence would read as a submission without matches. The stream is a function of its inputs: a run that adopted and one that judged publish the same events but for the adoption marks.

## Redesigned rather than ported

The prior implementation of this crate aligned revisions by a longest common subsequence over items, closed invalidation by a fixpoint over all pairs, took an append fast path that adopted a prefix on structural identity, and compared each reader's bindings by name against a footprint. Four defects followed from that design, and each is redesigned away rather than patched:

- **Over-adoption through values.** An answer could depend on a definition's value while only its type was compared. Here the support records what the judgement read, and the value-changed closure blocks type-position reads of changed values.
- **Non-termination under shadowing.** A shadowed definition made the definitional environment cyclic. Here every position resolves to one earlier reference, so no environment can be cyclic.
- **Super-linear rechecking.** Alignment and the closure were quadratic. Here every step is linear, and the census counts it.
- **A failed store that changed the store.** Here both stores encode first and the file store publishes by rename.

The append fast path and the alignment are gone: the memo recalls by content wherever an item moved, and the support decides reuse wherever it sits.

## Tests: the floor, the held rows, the defects

The prior implementation's 53 tests are the floor. Fifty exist here by name: the footprint's 5, the persistence suite's 15, the session's 2, the stream's 4, and the differential's 24 — 22 named edits and the two properties `incremental_equals_from_scratch` (one edit) and `edit_sequences_preserve_zero_drift` (one to four edits, each step resumed from the previous result and round-tripped through the codec). Each property runs 400 cases over programs of one to six statements named from a pool of six, with integer, string, thunk, reference and hole bodies and `Integer`, `String`, `U (F Integer)` and `El 0 name` ascriptions, under seven edit kinds: replace, insert, delete, a coordinated rename into a pool of eight names, swap, ascribe, and a value-only edit weighted three times the others.

Three are held until the vocabulary they test exists, with the rows of a fourth:

- `typed_static_family_arguments_round_trip` and `legacy_checkpoint_identity_is_rejected_after_static_family_move`: until the checker admits static families.
- `rung07_native_primitives_round_trip`: until the core vocabulary has native primitives.
- The module and package rows of `nested_process_local_and_opaque_forms_report_exact_errors`: until modules and packages exist; the test covers every sort the vocabulary has today.

The content table spells a universe's sort beside its level. The value universe keeps the tag it had before the sorts were spelled, and the computation universe and a universe at a sort parameter take fresh tags, so a checkpoint written before the families decodes the same after them; the two quotes and the computation decode take fresh tags beside their families. `universe_sorts_and_levels_round_trip` pins all three sorts at one level.

The four defects are each witnessed absent in `tests/defects.rs`: `the_generator_reaches_value_only_edits_under_type_position_reads` (a deterministic census holds the property's generator to the class), `a_shadowing_program_under_a_type_position_read_checks_and_terminates`, `items_visited_for_a_head_edit_grow_linearly` (counted, not timed), and `a_failed_store_leaves_the_store_as_it_was` (memory and file).

## Consumer and open rows

The first consumer is `gandr-surface-session`: it lowers each submission, hands the program to `IncrementalSession`, and reports the resume beside the dispatcher's composition of the same text.

Open: **session checkpoints in the storage tier.** `CheckpointStore` is the seam where the storage value plane takes over from the file store, persisting checkpoint sets as values with the storage tier's own integrity and retention.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
