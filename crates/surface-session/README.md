# gandr-surface-session

The interactive session: each revision of one source lowered, judged exactly as `gandr check` judges it, resumed through the incremental checker and checkpointed.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Session` takes successive revisions of one source through `Session::submit`, which is `Session::judge` then `Session::admit`. `judge` lowers each revision once; the dispatcher's `judge` judges and settles the lowered module, and the same declarations, offered by the item source as a `Program`, go to the incremental checker, which adopts every checkpoint that still answers, judges the rest and persists the set. `admit` then offers the judged declarations to the kernel, and the artifact of what crossed is committed into a block store as records through `gandr-storage-artifact`. The `Submission` carries the dispatcher's `Composed` and `Standing` for the text, the resume's census and whether the checkpoints were stored, the manifest of the kernel checkpoint, the edit actions from the latest accepted revision and the parse's completion obligations, and turns into the dispatcher's `Step` so a face renders it through the same renderer the batch verbs use. `Session::reopen` restores a session over the checkpoints an earlier one wrote, and `Session::read_kernel` reads a kernel checkpoint back through the kernel's decoder.

**Why.** The REPL, the language server and a terminal interface all need what the batch pipeline does not keep: the latest resume to adopt from, a checkpoint store that outlives the process, and the import scope of the last revision that lowered. Holding that state once, below every face, means each face is a loop over `submit` and a renderer of steps, and every face's verdicts are the batch pipeline's.

**How.** `judge` parses the revision through the session's form store, which molds only the top-level forms whose identity it does not hold, then calls the dispatcher's `lower_parsed`, then the dispatcher's `judge` for the report and `program` plus `IncrementalSession::submit` for the resume, over a copy of the lowered arena, and keeps the dispatcher's `Admission` for `admit`. A whole-revision refusal is `Composed::Refused`: it retains the accepted resume, imports, and snapshot but advances the lowering-attempt count. Checkpoints use `CheckpointStore`; a store failure becomes `Persistence::Failed` when a resume remains available, otherwise `SessionFault::Store`. A kernel block-store refusal is carried as `KernelCheckpoint::Failed` without discarding the accepted resume.

## Provided features

- **The session.** `Session`, `Session::new`, `Session::submit`, `Session::last`, `Session::stream`, `Session::lowerings`, `Session::into_store`; `Submission`, `Resumed`, `Persistence`, `resumed::Absent`, `SessionFault`.
- **The judgement before the admission.** `Session::judge`, `Session::admit`, `Admitted`, `admitted::Absent`, `admission::Absent`: a revision's report and resume before its kernel admission, and the admission after.
- **The form store.** `Submission::forms`, `FormCensus`, `FormCount`, `Session::with_width`: each submission's forms and how many were molded rather than taken up.
- **Trials.** `Session::trial`, `Trial`, `CandidateIndex`, `resumed::Absent::Tried`, `FormStore::parse_held`: candidate revisions judged against the latest accepted state without submitting any, each as a fresh session judges it, ranked, the session unchanged.
- **The step a face renders.** `Submission::into_step`: the submission as the dispatcher's `Step::Source`.
- **The parser's repairs.** `Submission::obligations`: the parse's completion obligations, in source order.
- **Checkpoints across processes.** `Session::reopen`, `Reopened`, `reopened::Absent`.
- **The kernel checkpoint.** `KernelCheckpoint`, `Submission::kernel`, `Session::read_kernel`, `Session::blocks`.
- **The import scope.** `Session::resolve_import`, `ImportRow`, `import::Absent`.
- **The item source.** `program`, `SurfaceItems` (an `ItemSource`), `Revision`, `RevisionFault`, `fault_span::Absent`.
- **Evaluation.** `Submission::evaluate`, `evaluate`, `evaluation::Absent`: a hole-free item run on the dispatcher's run stage.
- **Types and documentation.** `type_of`, `spelled::Absent`, `Session::documentation`: a declaration's type spelled at a page width from the latest resume, by name, and its documentation by its form's identity.
- **Edit-action reconstruction.** `Snapshot` (`of`, `items`, `node`, `span`, `localize`, `edit_locus`), `diff`, `apply`, `EditScript`, `Action`, `CorePath`, `ChildSlot`, `Tree`, `ItemTree`, `SourceEdit`, the reasons `addressed`, `spanned`, `located` and `body_path`; `Submission::edits`, `Session::snapshot`.

## Expected features

- **A checkpoint store.** Any `CheckpointStore`: `gandr-core-incremental`'s `MemoryCheckpointStore` for a session that dies with its process, its `FileCheckpointStore` for one that outlives it.
- **A block store.** Any `BlockStore`: `gandr-storage-records`' `InMemoryBlockStore` for a session that dies with its process; a store that outlives it carries the kernel checkpoints to the next.
- **A backend identity.** A `BackendArtifact` naming the checker build, so checkpoints a different checker judged are never restored.
- **The text.** The caller owns the source's buffer and submits each revision whole; the submission borrows it.
- **A face.** The dispatcher's `entries` reads the `Step` a submission turns into as `gandr-surface-diagnostics` diagnostics, which `gandr-surface-render-terminal` lays out and `gandr-surface-lsp` publishes.

## Examples

```rust
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_grammar::built_in;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;

let mut session = Session::new(
    built_in()?,
    SourceRoot::Strict,
    MemoryCheckpointStore::default(),
    InMemoryBlockStore::default(),
    BackendArtifact::from(b"this checker build".as_slice()),
);
let _first = session.submit(SourceText::from("def x = 40 ;"))?;
let second = session.submit(SourceText::from("def x = 40 ;\ndef y = x ;"))?;
// `second.composed()` is what `gandr check` reports for the text; its resume
// adopted the checkpoint of `x` and judged `y`, `second.edits()` holds the one
// action inserting `y`, and `second.kernel()` names the kernel checkpoint of
// both definitions, which `session.read_kernel` reads back.
```

The crate's tests run with `cargo nextest run -p gandr-surface-session`.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| A crate of its own, contract evidence, references | [`src/lib.rs`](src/lib.rs) |
| Submissions, trials, the report, the kernel admission, checkpoints, imports, repairs, diagnostics and goals, evaluation | [`session`](src/session.rs) |
| The form store | [`forms`](src/forms.rs) |
| The item source | [`item_source`](src/item_source.rs) |
| Edits as a diff of the lowered core, native snapshots, localization | [`edit`](src/edit.rs) |
| A declaration's type and documentation | [`typed`](src/typed.rs) |
| Live match checkpoints | [`live_match`](src/live_match.rs) |

The deferred behavioural floor — the named census and the live-match and pattern-hole suites — is tracked in [#211](https://github.com/gandr-lang/gandr/issues/211).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
