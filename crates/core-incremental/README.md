# gandr-core-incremental

Incremental checking over the core judgement: reuse applicable earlier answers and match batch checking when recorded results are faithful.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A front end hands over one `Program` per revision: `Item`s, each a front-end `ItemKey` beside the checker's own `Declaration`, over one `CoreArena`. `check_program` judges every item; `resume` takes the previous revision's `Resume` and answers the edited program, adopting each item's checkpoint only when it still answers and judging the rest. Checkpoints persist under their program's content address in a memory or an atomic file store, and a `SynthesisStream` publishes each item's handle, typing and adoption, then the match liveness its producer computed.

**Why.** A checker that answers an editor on every keystroke cannot judge the whole program each time, and a checker that reuses answers it cannot justify answers wrongly. This crate reuses only what the judgement itself says it depended on, compared value by value, so reuse is a saving and never a change of answer: incremental equals batch, and the tests hold it to that over generated programs and edit chains.

**How.** Batch and incremental are one forward pass at two memos. Each item is encoded once into id-free content; the memo recalls a base checkpoint of equal content; the checkpoint is adopted when every signature answer its judgement consulted equals the edited table's answer at that point of the pass, no type position of it reads a definition whose value changed, and its type can be seated in the edited arena. A type the recalled verdict checked or synthesised under is seated as that judgement formed it, with no formation walk; any other signature is formed again. A value change closes over readers once, through reverse read edges. Item identity across revisions rides on an order-maintenance structure from `gandr-theory-order-maintenance`.

## Provided features

- **The item seam.** `Program`, `Item`, `ItemKey`, `Reference`, `ItemSource`: items keyed by the front end, admission positions checked once (`ProgramError`), and every position read as the `Reference` — key and occurrence — it resolves to.
- **Content.** `ItemContent`, `TypeContent`, `ContentNode`, `SupportedNode`, `Opacity`: an item's or a type's nodes as one co-de Bruijn table numbered by discovery, free of arena ids — each entry a compact former with its scope, one thinning per child and the references beneath it, equal subterms one entry whatever the arena shared or whatever unused binders surround them; `debruijn` projects a root back to the de Bruijn table a printer or an open type's seat reads, reporting an index past `u32` rather than saturating, and a closed table, already its own de Bruijn table, seats as it stands. `TypeContent::of_value_type` reads a type, and a table holding an id its arena does not resolve is opaque. Term holes, marks and the unknown types are content like any former, and round-trip through the checkpoint codec under tags of their own. Witnesses: `content::tests::unused_binder_interleavings_share_one_node`, `content::tests::covers_preserve_every_binding_former`, `codec::tests::holes_marks_and_the_unknown_types_round_trip`.
- **Effect-row content.** Returners retain canonical interface and operation names and every payload and reply type as graph edges. Pure returners retain content tag `0x30`; nonempty rows use `0x70`. Decoding refuses duplicate or out-of-order names and an empty row under the nonempty tag. Witnesses: `content::tests::effect_rows_round_trip_without_losing_operation_types`, `codec::tests::effect_rows_persist_operation_types_and_canonical_identity` and `codec::tests::effect_rows_reject_duplicate_and_noncanonical_names`.
- **The conservative footprint.** `footprint_of` and `Footprint`: every reference an item mentions, those in type positions apart, its opacity and whether its body is a hole — the union of the references its roots carry, read off without a walk of the table. The references are syntactic and over-approximate; they never decide a strengthening. Witness: `tests::supports::carried_footprint_matches_reference_walk`.
- **Validated resume.** `check_program`, `resume`, `resume_from`, `Resume`, `Checkpoints`, `ItemCheckpoint`, `Answered`, `Answer`, `Adoption`, `ResumeCensus`, and `project`, which turns a verdict of the checker's own batch entry into the `Typing` this crate records, so a caller can compare the two. Filling a term hole is a body edit: the filled item is judged, and an item is rejudged only when an answer it consulted changed — a reader of a declared type is adopted, a reader of the unknown type an unsigned hole synthesised is not. Witness: `tests::incremental::filling_a_hole_rejudges_only_what_its_support_mentions`.
- **Item identity.** `ItemHandle` and `Resume::compare`: a handle per item that survives edits elsewhere and compares in constant time.
- **Resuming after leading items.** `lead`, `Leading`, `resume_after`: `lead` judges a program and keeps the state its last item leaves; a revision that lays that program's items first resumes after them, encoding, recalling and judging only its own items in the context they left. A revision that departs from them is resumed whole. A resume restored from a store whose first checkpoints are the state's recalls its own items after them as one held after that state does. Witnesses: `tests::incremental::a_revision_after_its_leading_items_judges_only_its_own_776`, `tests::incremental::a_restored_set_resumes_after_the_leading_items_it_holds_1816`.
- **Checkpoints and stores.** `encode_checkpoints`, `decode_checkpoints`, `CheckpointBytes`, `UnsupportedPersistence`, `address_of`, `persist`, `restore`, `CheckpointStore`, `MemoryCheckpointStore`, `FileCheckpointStore`, `DiscardingCheckpointStore`, `Keeping`, `CheckpointObserver`, `BackendArtifact`, `CheckpointAddress`, `CheckpointStoreError`, `Restorer`, `RestoreFrom`. A session over a store that keeps nothing (`CheckpointStore::KEEPING`) never addresses or encodes a set for it. `FileCheckpointStore::prune` removes every record another backend judged. Witness: `persistence::tests::pruning_keeps_only_the_kept_backend_s_records_1816`.
- **The session.** `IncrementalSession` and `SessionError`: one call per revision that resumes, persists and keeps the latest resume for streaming; `IncrementalSession::submit_after` submits a revision laid after a leading state. `submit_retiring` and `submit_after_retiring` poll a `gandr_core_checker::Retirement` before each item; a retired submission persists nothing and the session keeps the resume it held. Witness: `session::tests::a_retired_submission_keeps_the_resume_it_held_1547`. `IncrementalSession::persist_to` persists the held set to a store other than the session's, and `IncrementalSession::restore_from` has the next submission, when no resume is held, start from the set a `Restorer` holds for its program: what an editor's save keeps and its next open reads back. Witness: `session::tests::a_held_set_persists_to_another_store_and_restores_a_first_submission_1816`. `Handed` is the restorer of a set an earlier revision judged, held in memory and resumed from by a later revision's first submission whatever its program, adopting each item as a predecessor's: what an editor's copy hands the next copy of its document. Witness: `session::tests::a_set_handed_on_resumes_a_later_revision_s_first_submission_2102`.
- **Content keys.** `content_keys` and `ContentKey`: each item's key, the digest of its id-free content, which a pool keys the work on an item by. Witness: `checkpoint::tests::an_item_s_content_key_moves_only_with_its_content_1547`.
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

## References

- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: a stored `FootprintsOverlap` keeps both halves' footprints and what they share.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
