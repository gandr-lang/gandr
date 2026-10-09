# gandr-surface-session

The interactive session: each revision of one source lowered, judged exactly as `gandr check` judges it, resumed through the incremental checker and checkpointed.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [A crate of its own, above the dispatcher](#a-crate-of-its-own-above-the-dispatcher)
- [A submission is a whole revision the caller owns](#a-submission-is-a-whole-revision-the-caller-owns)
- [The report is the dispatcher's composition](#the-report-is-the-dispatchers-composition)
- [Refusals are the report](#refusals-are-the-report)
- [The item source](#the-item-source)
- [Checkpoints](#checkpoints)
- [The import scope persists across submissions](#the-import-scope-persists-across-submissions)
- [Tests: the floor, the deferred rows, the defects](#tests-the-floor-the-deferred-rows-the-defects)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `Session` takes successive revisions of one source through `Session::submit`. Each revision is lowered once; the dispatcher's `judge_module` judges, readmits and settles the lowered module, and the same declarations, offered by the item source as a `Program`, go to the incremental checker, which adopts every checkpoint that still answers, judges the rest and persists the set. The `Submission` carries the dispatcher's `Composed` and `Standing` for the text, the resume's census and whether the checkpoints were stored, and turns into the dispatcher's `Step` so a face renders it through the same renderer the batch verbs use. `Session::reopen` restores a session over the checkpoints an earlier one wrote.

**Why.** The REPL, the language server and a terminal interface all need what the batch pipeline does not keep: the latest resume to adopt from, a checkpoint store that outlives the process, and the import scope of the last revision that lowered. Holding that state once, below every face, means each face is a loop over `submit` and a renderer of steps, and every face's verdicts are the batch pipeline's.

**How.** `submit` calls the dispatcher's `lower_source`, then `judge_module` for the report and `program` plus `IncrementalSession::submit` for the resume, over a copy of the lowered arena. A revision the lowering refuses as a whole is reported as `Composed::Refused` and leaves the session as it was. Checkpoints go through `gandr-core-incremental`'s `CheckpointStore`, memory or file; a store's failure is reported in the submission as `Persistence::Failed`, never raised.

## References

- Microsoft. "Language Server Protocol Specification, version 3.17." 2022. <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — full-document synchronisation, the shape a submission takes: the client owns the buffer and sends it whole.

## Provided features

- **The session.** `Session`, `Session::new`, `Session::submit`, `Session::last`, `Session::stream`, `Session::lowerings`, `Session::into_store`; `Submission`, `Resumed`, `Persistence`, `resumed::Absent`, `SessionFault`. Witnesses: `tests::corpus::every_source_submits_as_the_walk_composes_it`, `tests::session::whole_file_submit_carries_definitions_forward`, `tests::session::successful_submissions_publish_whole_program_synthesis`, `tests::session::failed_submission_retains_latest_synthesis`.
- **The step a face renders.** `Submission::into_step`: the submission as the dispatcher's `Step::Source`. Witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`.
- **Checkpoints across processes.** `Session::reopen`, `Reopened`, `reopened::Absent`. Witnesses: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`, `tests::checkpoint::a_store_holding_nothing_reopens_fresh`, `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`.
- **The import scope.** `Session::resolve_import`, `ImportRow`, `import::Absent`. Witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`.
- **The item source.** `program`, `SurfaceItems` (an `ItemSource`), `Revision`, `RevisionFault`, `fault_span::Absent`. Witnesses: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`, `tests::items::the_item_source_offers_a_revision_or_names_its_fault`.

## Expected features

- **A checkpoint store.** Any `CheckpointStore`: `gandr-core-incremental`'s `MemoryCheckpointStore` for a session that dies with its process, its `FileCheckpointStore` for one that outlives it.
- **A backend identity.** A `BackendArtifact` naming the checker build, so checkpoints a different checker judged are never restored.
- **The text.** The caller owns the source's buffer and submits each revision whole; the submission borrows it.
- **A renderer.** `gandr-surface-diagnostics` renders the `Step` a submission turns into.

## Examples

```rust
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_grammar::built_in;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;

let mut session = Session::new(
    built_in()?,
    SourceRoot::Strict,
    MemoryCheckpointStore::default(),
    BackendArtifact::from(b"this checker build".as_slice()),
);
let _first = session.submit(SourceText::from("def x = 40 ;"))?;
let second = session.submit(SourceText::from("def x = 40 ;\ndef y = x ;"))?;
// `second.composed()` is what `gandr check` reports for the text; its resume
// adopted the checkpoint of `x` and judged `y`.
```

The crate's tests run with `cargo nextest run -p gandr-surface-session`.

## A crate of its own, above the dispatcher

The session owns incremental state and checkpoints the batch pipeline has no use for, and three faces read it. It sits in `surface` after the dispatcher and the diagnostics renderer and depends on the dispatcher and below, never on a face.

The alternatives were the dispatcher, which would carry state its `check` and `test` verbs never read, and the first face, which would leave the second to duplicate it. The choice reverses if one face remains the only reader; the session would then fold into it.

## A submission is a whole revision the caller owns

`submit` takes the full text of a revision and returns a `Submission` borrowing it; the session keeps no text. A face that reads lines appends them to its own buffer and submits the buffer, so a later "line" is the earlier revision with the line added, and what carries across lines is what the session keeps: the resume it adopts from and the import scope.

The prior implementation appended each submission to a transcript the session owned. Here the lowering resolves a name only within its own module, so a line alone could not see the definitions before it, and a report borrowing a session-owned buffer would freeze the session until the report was dropped. The choice reverses when the lowering takes a seed of earlier declarations: the session then owns the line-append, and a submission is the line.

## The report is the dispatcher's composition

The report a submission carries is `judge_module`'s, the second half of the composition `gandr check` runs, over the module `lower_source` read — so a submission and a walk step agree by construction, and the corpus agreement suite checks it source by source. The resume runs beside it over a copy of the arena.

The alternative was a report assembled from the resume's own verdicts. The incremental checker keeps typings, not the checker's verdicts, and a settle report is built from a judged module; assembling one from adopted checkpoints would be a second judgement to keep in agreement with the first. The cost of the choice is one arena copy and one whole-module judgement per accepted revision. It reverses when a step can be assembled from adopted checkpoints; the whole-module judgement and the copy retire then.

## Refusals are the report

The prior implementation lowered totally, degrading what it could not lower to an unknown type, and that accepted wrong programs. The reboot has no unknown former: a declaration the lowering refuses is reported as refused and offered to no one, a declaration the checker refuses is reported as refused and resumed as `Typing::Refused`, and a revision the lowering refuses as a whole is reported and leaves the session unchanged. A fault — a tree the parser cannot commit, a lowering or kernel disagreement — is a `SessionFault`, never a verdict about the source.

## The item source

`program` keys each declaration the lowering did not refuse by its name as written and carries exactly the declaration the dispatcher's `adapt` gives the checker, in admission order; refused declarations are left out and the admission positions skip them. The incremental checker therefore resumes over the declarations the batch judgement checks and no other. `SurfaceItems` is the same lowering behind `gandr-core-incremental`'s `ItemSource`; because that seam's error cannot borrow the revision, a whole-revision refusal crosses it as its failure class and span.

## Checkpoints

Every accepted submission persists its checkpoints under its program's content address. A store that fails leaves itself as it was and the session resuming from the submission; the submission reports `Persistence::Failed` and the next one adopts as usual. `Session::reopen` lowers the revision it is given, restores what the store holds for that program and backend, and resumes from it; a store holding nothing for it, or holding another backend's set, reopens fresh and says why. A restored set is not trusted: the next resume validates each checkpoint as it validates an in-memory one.

## The import scope persists across submissions

The session keeps the import rows and alias scope of the last revision the lowering read, owned so they outlive its text. A revision the lowering refuses — one that declares an alias twice among them — leaves the scope of the revision before it, so a face resolving `parse` keeps its answer while the author repairs the collision.

## Tests: the floor, the deferred rows, the defects

The prior implementation's session, incremental, edit, diagnostics and goals suites, with the tests beside their source, are the floor: 162 tests. A row over a former the fragment does not have is deferred by name with that former.

| Suite | Floor | Here | Deferred |
| ----- | ----- | ---- | -------- |
| session, beside the source | 9 | 3 | 6 |
| session | 42 | 9 | 33 |
| incremental | 13 | 9 | 4 |

The ported rows keep their names. A row whose prior form also evaluated its item keeps its typing half here; evaluation is deferred with the machine. `scalar_literals_carry_their_types` covers integer and string literals; the suffixed numeric literal is outside the fragment. The incremental property `incremental_equals_from_scratch` runs a chain of one to four edits per case, 200 cases, over revisions of one to six statements from a pool of six names with integer, string, reference, thunk, function-applying thunk, function-tail and signature-only bodies and `Integer`, `String` and `U (F Integer)` signatures, under replace, insert, delete, coordinated rename, swap, ascribe and value-only edits; each step's report must equal the dispatcher's and its typings the checker's module entry.

Deferred, with the former each needs:

- Path types and definitional unfolding: `a_definition_reaches_the_typing_context_chain`, `a_law_over_a_definition_types_from_source`, `a_law_over_a_definition_types_when_both_arrive_in_one_source`, `a_law_over_a_definition_that_returns_otherwise_is_refused`.
- Graded thunk types: `a_graded_bridge_signature_is_an_abstention_not_a_refusal`.
- Dependent binders at the surface: `a_dependent_signature_is_an_abstention_not_a_refusal`.
- Sum types and `case`: `one_part_case_bodied_function_checks_and_evaluates`, `erased_sum_definition_is_consumed_by_a_later_case`.
- Evaluation: `integer_literal_types_and_evaluates`, `nullary_function_call_evaluates`, `holes_decline_evaluation` (with typed holes).
- The unknown type, absent by construction: `computation_top_result_types_binds_and_applies`, `value_unknown_ascription_types_and_evaluates`.
- Operators and the builtin prelude: `arithmetic_operators_type_check_and_evaluate`, `operator_definition_carries_across_lines`, `module_builtins_type_and_evaluate`, `comparison_operators_type_check_and_evaluate`, `boolean_operators_type_check_and_evaluate`, `string_builtin_type_and_evaluate`, `string_contains_scans_conflict_marker_text`, `rung07_builtins_type_check_and_evaluate`, `rung07_builtin_failures_are_gradual_blame`, `rung07_wrong_shape_calls_are_static_type_errors`, `regex_builtin_type_and_evaluate`, `regex_extract_failures_are_gradual_blame`, `an_unknown_prelude_member_is_declined_as_a_hole`.
- Lists: `list_concat_type_checks_and_evaluates`, `lists_need_an_annotation_then_evaluate`, `list_each_maps_a_closure_over_a_list`, `list_reduce_folds_a_list`, `list_functional_update_builtins_evaluate`, `out_of_bounds_list_update_blames`, `list_any_and_sort_evaluate`, `list_where_filters_by_a_predicate`.
- Records: `record_get_and_insert_evaluate`, `record_update_rebuilds_a_fresh_record`.
- Computation ascription in expression position: `computation_ascription_types_and_evaluates_check_only_forms`.
- Foreign declarations: `extern_declaration_carries_across_lines_and_a_foreign_call_blames_without_a_handler`.
- Module declarations: `a_hidden_or_absent_user_module_component_is_declined_as_a_hole`.
- Typed holes in `case` patterns: `filling_a_pattern_hole_resumes_to_the_written_source`, `opening_a_pattern_hole_resumes_to_the_unfinished_source`, `filling_a_hole_invalidates_only_the_item_holding_it`, `a_type_stable_fill_adopts_its_dependent`.

Two defects of the prior implementation are absent. A submission panicked on a corpus source the walk passed: absent at L2, since `tests::corpus::every_source_submits_as_the_walk_composes_it` submits every source of both roots whole and compares each with the walk's step. Total lowering accepted wrong programs through the unknown type: absent by construction, since no unknown former exists.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
