# gandr-core-incremental

Incremental checking over the core judgement: reuse applicable earlier answers and match batch checking when recorded results are faithful.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A front end hands over one `Program` per revision: `Item`s, each a front-end `ItemKey` beside the checker's own `Declaration`, over one `CoreArena`. `check_program` judges every item; `resume` takes the previous revision's `Resume` and answers the edited program, adopting each item's checkpoint only when it still answers and judging the rest. Checkpoints persist under their program's content address in a memory or an atomic file store, and a `SynthesisStream` publishes each item's handle, typing and adoption, then the match liveness its producer computed.

**Why.** A checker that answers an editor on every keystroke cannot judge the whole program each time, and a checker that reuses answers it cannot justify answers wrongly. This crate reuses only what the judgement itself says it depended on, compared value by value, so reuse is a saving and never a change of answer: incremental equals batch, and the tests hold it to that over generated programs and edit chains.

**How.** Batch and incremental are one forward pass at two memos. Each item is encoded once into id-free content; the memo recalls a base checkpoint of equal content; the checkpoint is adopted when every signature answer its judgement consulted equals the edited table's answer at that point of the pass, no type position of it reads a definition whose value changed, and its type can be seated in the edited arena. A value change closes over readers once, through reverse read edges. Item identity across revisions rides on an order-maintenance structure from `gandr-theory-orders`.

## Provided features

- **The item seam.** `Program`, `Item`, `ItemKey`, `Reference`, `ItemSource`: items keyed by the front end, admission positions checked once (`ProgramError`), and every position read as the `Reference` — key and occurrence — it resolves to.
- **Content.** `ItemContent`, `TypeContent`, `ContentNode`, `SupportedNode`, `Opacity`: an item's or a type's nodes as one co-de Bruijn table numbered by discovery, free of arena ids — each entry a compact former with its scope, one thinning per child and the references beneath it, equal subterms one entry whatever the arena shared or whatever unused binders surround them; `debruijn` projects a root back to the de Bruijn table a printer or an open type's seat reads, reporting an index past `u32` rather than saturating, and a closed table, already its own de Bruijn table, seats as it stands. `TypeContent::of_value_type` reads a type, and a table holding an id its arena does not resolve is opaque. Term holes, marks and the unknown types are content like any former, and round-trip through the checkpoint codec under tags of their own. Witnesses: `content::tests::unused_binder_interleavings_share_one_node`, `content::tests::covers_preserve_every_binding_former`, `codec::tests::holes_marks_and_the_unknown_types_round_trip`.
- **Effect-row content.** Returners retain canonical interface and operation names and every payload and reply type as graph edges. Pure returners retain content tag `0x30`; nonempty rows use `0x70`. Decoding refuses duplicate or out-of-order names and an empty row under the nonempty tag. Witnesses: `content::tests::effect_rows_round_trip_without_losing_operation_types`, `codec::tests::effect_rows_persist_operation_types_and_canonical_identity` and `codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`.
- **The conservative footprint.** `footprint_of` and `Footprint`: every reference an item mentions, those in type positions apart, its opacity and whether its body is a hole — the union of the references its roots carry, read off without a walk of the table. The references are syntactic and over-approximate; they never decide a strengthening. Witness: `tests::supports::carried_footprint_matches_reference_walk`.
- **Validated resume.** `check_program`, `resume`, `resume_from`, `Resume`, `Checkpoints`, `ItemCheckpoint`, `Answered`, `Answer`, `Adoption`, `ResumeCensus`, and `project`, which turns a verdict of the checker's own batch entry into the `Typing` this crate records, so a caller can compare the two. Filling a term hole is a body edit: the filled item is judged, and an item is rejudged only when an answer it consulted changed — a reader of a declared type is adopted, a reader of the unknown type an unsigned hole synthesised is not. Witness: `tests::incremental::filling_a_hole_rejudges_only_what_its_support_mentions`.
- **Item identity.** `ItemHandle` and `Resume::compare`: a handle per item that survives edits elsewhere and compares in constant time.
- **Checkpoints and stores.** `encode_checkpoints`, `decode_checkpoints`, `CheckpointBytes`, `UnsupportedPersistence`, `address_of`, `persist`, `restore`, `CheckpointStore`, `MemoryCheckpointStore`, `FileCheckpointStore`, `CheckpointObserver`, `BackendArtifact`, `CheckpointAddress`, `CheckpointStoreError`.
- **The session.** `IncrementalSession` and `SessionError`: one call per revision that resumes, persists and keeps the latest resume for streaming; `IncrementalSession::submit_seeded` lets a session's first revision resume from checkpoints a caller already holds.
- **The synthesis stream.** `SynthesisStream`, `SynthesisEvent`, `Liveness`, `MatchOrigin`; branch verdicts are `gandr_core_term::pattern::BranchStatus`, the vocabulary live matching and coverage answer in.

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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The incremental specification and validated resume | [`checkpoint`](src/checkpoint.rs) |
| References, content, the co-de Bruijn table and handles | [`region`](src/region.rs), [`content`](src/content.rs), [`support`](src/support.rs), [`order`](src/order.rs) |
| Native, recursive and control content and their cache tags | [`content`](src/content.rs) |
| The canonical encoding | [`codec`](src/codec.rs) |
| Stores, their addresses and atomicity | [`persistence`](src/persistence.rs) |
| The synthesis stream | [`stream`](src/stream.rs) |
| Sessions | [`session`](src/session.rs) |
| Specification evidence, the consumer and references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
