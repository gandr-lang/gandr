# gandr-core-incremental

Incremental checking over the core judgement: reuse applicable earlier answers and match batch checking when recorded results are faithful.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The incremental specification](#the-incremental-specification)
- [Identity: references, content, handles](#identity-references-content-handles)
- [Validated resume](#validated-resume)
- [Checkpoints and their stores](#checkpoints-and-their-stores)
- [The synthesis stream](#the-synthesis-stream)
- [Native universe-path content](#native-universe-path-content)
- [Specification evidence](#specification-evidence)
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

## The incremental specification

**Support is an output of the judgement.** The checker reports, for each declaration it judges, every signature answer it consulted: the reference asked about and the answer given, the type's content or none. That list is the item's support, and a checkpoint stores it. Reuse is licensed by comparing it, entry by entry, against the answers the edited program's table gives at the same point of the pass. Nothing else licenses reuse: not a footprint, not a name, not an edit's location. A footprint over-approximates what an item could read; the support is what it did read, which is both tighter and exact.

**The entry answers one item.** The checker's per-declaration entry judges one declaration against the table the preceding items built, so the pass interleaves judging and adopting in source order (`CheckingContext::adopt`). The supplied signature answer is assembled at adoption rather than stored separately: a signed item's signature forms in the edited context; an unsigned item's cached synthesised type is seated and forms there. Formation establishes that the type is usable in that context, not that an arbitrary cached type was correctly inferred for the body.

**Incremental equals batch for faithful records.** `check_program` is the pass at a memo that recalls nothing; `resume` is the same pass at a memo that recalls base checkpoints. Batch equivalence assumes that each recorded typing and complete support truthfully describes a prior judgement of that content under the recorded allowance. Raw constructors and mutation helpers admit arbitrary records: reuse checks establish applicability, not the truth of a cached judgement. The differential suite compares faithful resumes with the checker's module entry and deliberately forges typing and support to witness this boundary. Canonical bytes and integrity digests do not authenticate judgement provenance.

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
3. No reference in a type position of the item, nor in the type of any recorded answer, names a definition in the value-changed set. A type former's own reference is in a type position, including an abstract type under quotation.
4. The adopted type seats: a signed item's signature forms in the edited context; an unsigned item's synthesised type is minted into the edited arena before the pass and forms.

**The value-changed set.** A definition inserted, deleted, or whose content differs between the revisions seeds the set; the set closes over the read relation of the edited footprints through reverse edges and a worklist, so every edge is crossed at most once. Once the set is non-empty every opaque item joins it. The closure guards answers that depend on a definition's _value_ while the support compares types: the checker unfolds a decode `El(c)` of a code constant to the body `c` was defined with, and logs the constant's signature answer, not its body, so a declaration whose type names `c` can change meaning while every recorded answer holds. The closure blocks exactly those reuses. When the checker records the bodies it unfolds in the support, the closure can retire.

**Linear by construction.** Each item is encoded once, recalled at most once, adopted or judged once; the closure crosses each read edge at most once; the splice is one map build and one patience walk. `ResumeCensus` counts each of these, and a test pins the counts for a head edit of chains from 250 to 2,000 items.

| Decision | Alternatives | Reversal |
| -------- | ------------ | -------- |
| Pointwise support recorded by the judgement | compare bindings by name; compare footprints; re-judge every reader of an edited item | none: this is the soundness argument |
| Mint an unsigned item's synthesised type into the edited arena before the pass | judge every unsigned item a recalled reader depends on | minting dominates a measured profile |
| Close value changes over footprint reads, blocking type-position reads | no closure, trusting the signature answers alone, which reuses a declaration across an edit to a code it unfolds | the checker records the bodies it unfolds in the support |
| Derive supplied answers from the formed signature or seated cached type | store a second answer beside the typing | a consumer needs an independently certified answer |
| Trust faithful checker results, then validate their applicability | re-judge every cached item; proof-carrying judgement certificates | checkpoints must be accepted from an untrusted producer |

## Checkpoints and their stores

**One canonical encoding.** A checkpoint set encodes to one byte string: magic, allowance, then each item’s content, footprint, support and typing, with sets ascending and tables in discovery order. Content producers establish the table invariants; the decoder checks them. Before framing, a borrowed pass refuses any level atom whose offset reaches 4,096, in the content, support or typing. The decoder enforces the same bound because it reconstructs each offset with that many successors. It also refuses truncated, malformed and trailing bytes, and any payload that parses but is not the canonical spelling of its value. After the level check, encoding names the sort of its first unresolved id (`UnsupportedPersistence::Dangling`); opaque content has no spelling.

**Addressed by program, keyed by backend.** A set is stored under the BLAKE3 digest of its program's canonical bytes and the identity of the backend artifact that judged it, so it is only restored for the same program and the same checker. A restored set is validated by the next resume like any other.

**A failed store leaves the store as it was.** Both stores encode completely before they change anything, so a capped level cannot replace a readable record. The file store writes the record — header with magic, version, address, backend, length and payload digest, then the payload — to a temporary it created exclusively under a fresh random name, publishes it with one rename, and attempts to remove the temporary on every other exit; it never opens a file it did not create. Cleanup is best effort: a removal failure can leave a private temporary. Loading checks the header, the address, the length and the digest before decoding. The store is atomic, not durable: it does not synchronise to the device.

| Decision | Alternatives | Reversal |
| -------- | ------------ | -------- |
| A crate-local canonical binary encoding with a canonicality check | a serialisation framework, which would add a dependency and admit several spellings of one value | the storage tier hosts session checkpoints (below) |
| Check the decoder’s level bound before checkpoint encoding | publish records that cannot reload; unbounded decoding; decode an extra copy before storing | level reconstruction no longer requires one successor per offset and the decoder can safely admit the full range |
| BLAKE3 through the workspace `blake3` entry, the digest the storage tier uses | the storage tier's digest wrapper, which a `core` crate cannot depend on under the layering; a second hash function | the digest moves to a layer below both |
| Exclusive temporary, then rename | write in place; a fixed temporary name, which a squatter or a concurrent store could hijack | a consumer needs durability, which adds a sync before and after the rename |

## The synthesis stream

A stream opens with the item count, carries one event per item in source order — its handle, typing and adoption — then the match liveness its producer computed, by origin, and closes. Liveness follows the items because a match is addressed by source coordinates and one source item may lower to several core items. A submission whose source records are gone is named by an event of its own, because silence would read as a submission without matches. The stream is a function of its inputs: a run that adopted and one that judged publish the same events but for the adoption marks.

## Native universe-path content

The content table preserves universe sorts and levels, quotes, static operators and native universe paths. Native path tags occupy `0x40–0x44` in this cache codec; they are not kernel artifact tags. Candidate evidence is exact content, including ordered direction and dialogue boundaries, and never a cached admission receipt. Type-only signature content refuses term-bearing path classifiers just as it refuses quotes and decodes.

Checkpoint sets use `GCKPT\0\0\x04`; programs use `GPROG\0\0\x02`. Their identities bind the current checker and refusal vocabulary, including admitted sums, checking-only injection and case, and invalid path-code refusals. Earlier identities are rejected rather than reusing answers from a different fragment. Static family and universe round-trip witnesses continue to exercise their distinct tags and payloads.

**Choice.** Preserve native classifiers, maps and candidate evidence as content instead of caching a certificate verdict. Structural path conversion may erase evidence, but checkpoint identity must not. **Reversal.** Persisting `Flow_U`, element identity, the bridge mode, higher fields, funext or guarded List inhabitants requires its own versioned content vocabulary and validated dependency support; none is inferred from a native path entry.

## Specification evidence

Item-level `#[spec]` predicates check observable boundaries and transitions. Each `# Adequacy` section names its witness and bounds the claim; a data declaration, abstract protocol or unsupported opaque return states why it has no executable predicate. Generated differential cases support a finite-domain claim, not a proof over every program.

| Evidence | Witness surface | Boundary |
| -------- | --------------- | -------- |
| Batch equivalence and real adoption | [differential suite](tests/incremental.rs) | faithful records, named edits, generated single edits and edit chains; forged records expose the trust premise |
| Edit and lowering semantics | [common fixtures](tests/common.rs), [generator](tests/generate.rs) | forward and shadowed names, maximal literals, missing indices, clamped insertion, coordinated rename and modular integer selection |
| Type-position dependencies | [footprints](src/footprint.rs), [checkpoint guards](src/checkpoint.rs) | quoted abstract types, recorded-answer types, cycles and opaque readers |
| Canonical representation | [content](src/content.rs), [codec](src/codec.rs) | all supported node sorts, graph discovery, payloads, malformed tags, lengths and canonicality |
| Store failure atomicity | [persistence](src/persistence.rs), [defect witnesses](tests/defects.rs) | dangling ids and capped levels preserve existing records; filesystem cleanup remains best effort |
| Reachability and work | [defect witnesses](tests/defects.rs) | deterministic value-only-edit census, shadowing termination and exact work counts for chains of 250 through 2,000 items; zero-length chains are empty |
| Session and stream transitions | [session](src/session.rs), [stream](src/stream.rs) | retained state on failure, item ordering, liveness and terminal events |

The content vocabulary includes sorted universes, quotes, decodes, static operators and native paths. A static Pi seats as a value type; static lambdas, applications and quotes are terms, not seatable types. The [native content format](#native-universe-path-content) binds that vocabulary and its refusal payloads; another magic is rejected rather than interpreted under different tags. Native primitives, modules and packages are outside this crate’s current vocabulary.

## Consumer and open rows

The first consumer is `gandr-surface-session`: it lowers each submission, hands the program to `IncrementalSession`, and reports the resume beside the dispatcher's composition of the same text.

Open: **session checkpoints in the storage tier.** `CheckpointStore` is the seam where the storage value plane takes over from the file store, persisting checkpoint sets as values with the storage tier's own integrity and retention.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
