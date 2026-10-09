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
- [Edits are a diff of the lowered core](#edits-are-a-diff-of-the-lowered-core)
- [Localization descends extents](#localization-descends-extents)
- [The parse's repairs ride beside the step](#the-parses-repairs-ride-beside-the-step)
- [Diagnostics and goals are the renderer's](#diagnostics-and-goals-are-the-renderers)
- [Tests: the floor, the deferred rows, the defects](#tests-the-floor-the-deferred-rows-the-defects)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `Session` takes successive revisions of one source through `Session::submit`. Each revision is lowered once; the dispatcher's `judge_module` judges, readmits and settles the lowered module, and the same declarations, offered by the item source as a `Program`, go to the incremental checker, which adopts every checkpoint that still answers, judges the rest and persists the set. The `Submission` carries the dispatcher's `Composed` and `Standing` for the text, the resume's census and whether the checkpoints were stored, the edit actions from the latest accepted revision and the parse's completion obligations, and turns into the dispatcher's `Step` so a face renders it through the same renderer the batch verbs use. `Session::reopen` restores a session over the checkpoints an earlier one wrote.

**Why.** The REPL, the language server and a terminal interface all need what the batch pipeline does not keep: the latest resume to adopt from, a checkpoint store that outlives the process, and the import scope of the last revision that lowered. Holding that state once, below every face, means each face is a loop over `submit` and a renderer of steps, and every face's verdicts are the batch pipeline's.

**How.** `submit` calls the dispatcher's `lower_source`, then `judge_module` for the report and `program` plus `IncrementalSession::submit` for the resume, over a copy of the lowered arena. A revision the lowering refuses as a whole is reported as `Composed::Refused` and leaves the session as it was. Checkpoints go through `gandr-core-incremental`'s `CheckpointStore`, memory or file; a store's failure is reported in the submission as `Persistence::Failed`, never raised.

## References

- Microsoft. "Language Server Protocol Specification, version 3.17." 2022. <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — full-document synchronisation, the shape a submission takes: the client owns the buffer and sends it whole.
- Porter et al. "Incremental Bidirectional Typing via Order Maintenance." arXiv:2504.08946, 2025. <https://arxiv.org/abs/2504.08946> — an incremental checker that consumes structured edit actions rather than text, the input edit reconstruction produces.
- Hunt, J. W., and Szymanski, T. G. "A Fast Algorithm for Computing Longest Common Subsequences." Communications of the ACM 20(5), 1977. — the reduction of a longest common subsequence over distinct keys to a longest increasing subsequence, which item alignment uses.

## Provided features

- **The session.** `Session`, `Session::new`, `Session::submit`, `Session::last`, `Session::stream`, `Session::lowerings`, `Session::into_store`; `Submission`, `Resumed`, `Persistence`, `resumed::Absent`, `SessionFault`. Witnesses: `tests::corpus::every_source_submits_as_the_walk_composes_it`, `tests::session::whole_file_submit_carries_definitions_forward`, `tests::session::successful_submissions_publish_whole_program_synthesis`, `tests::session::failed_submission_retains_latest_synthesis`.
- **The step a face renders.** `Submission::into_step`: the submission as the dispatcher's `Step::Source`. Witnesses: `tests::corpus::every_source_submits_as_the_walk_composes_it`, `tests::diag::error_corpus_reports_match_goldens`, `tests::diag::goal_corpus_reports_match_goldens`.
- **The parser's repairs.** `Submission::obligations`: the parse's completion obligations, in source order. Witnesses: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`, `tests::diag_obligations::rows_are_in_source_order_not_severity_order`, `tests::diag_obligations::a_clean_source_reports_no_obligations`.
- **Checkpoints across processes.** `Session::reopen`, `Reopened`, `reopened::Absent`. Witnesses: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`, `tests::checkpoint::a_store_holding_nothing_reopens_fresh`, `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`.
- **The import scope.** `Session::resolve_import`, `ImportRow`, `import::Absent`. Witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`.
- **The item source.** `program`, `SurfaceItems` (an `ItemSource`), `Revision`, `RevisionFault`, `fault_span::Absent`. Witnesses: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`, `tests::items::the_item_source_offers_a_revision_or_names_its_fault`.
- **Edit-action reconstruction.** `Snapshot` (`of`, `items`, `node`, `span`, `localize`, `edit_locus`), `diff`, `apply`, `EditScript`, `Action`, `CorePath`, `ChildSlot`, `Tree`, `ItemTree`, `SourceEdit`, the reasons `addressed`, `spanned`, `located` and `body_path`; `Submission::edits`, `Session::snapshot`. Witnesses: `tests::edit::apply_of_diff_reproduces_new`, `tests::edit::literal_edit_is_one_set_int`, `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`, `tests::edit::a_submission_carries_the_edits_from_the_last_accepted_revision`, `edit::tests::descent_agrees_with_the_linear_stab_oracle`.

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
// adopted the checkpoint of `x` and judged `y`, and `second.edits()` holds the
// one action inserting `y`.
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

## Edits are a diff of the lowered core

Each accepted submission carries the `EditScript` from the latest accepted revision: the `diff` of their `Snapshot`s. A snapshot reads each item's signature and body out of the arena as a `Tree` of the incremental checker's `ContentNode`s, numbered breadth-first, each constant read as the `Reference` it resolves to, so two revisions lowered into two arenas compare node by node. Items align by reference — key and occurrence — keeping the largest set whose order both revisions share; each kept pair's bodies are walked together, a changed literal, variable or constant becoming one in-place action and any other change one `Replace` of the old subtree. `apply` of a diff to the old items reproduces the new ones exactly: soundness is total, localization is partial. A path names an item and the child slots from its body's root; an action anchored in the old revision carries the old ordinal, an insertion the new one.

The recorded design is this contract over the prior implementation's named surface core, with actions for grades, injection sides, binder names and annotations, and items aligned by a longest common subsequence of their names in an `n·m` table. The core here carries none of those payloads — binders are de Bruijn indices, so renaming one reconstructs to no action — and its actions are the core's own leaves. Because references are unique within a revision, the longest common subsequence is the longest increasing run of matched old ordinals, which patience sorting finds in `n log n`. The alternatives were a text diff, which names bytes rather than terms, and a diff of content-addressed tables, which numbers nodes and loses the path a face surfaces. The choice reverses when the lowering emits structured edits itself; the session would then forward them.

## Localization descends extents

`Snapshot::localize` returns the body node whose span encloses a range with the fewest bytes, the outermost of a shared span and the leftmost at one depth — the prior implementation's rule, so a contiguous edit's locus is the common ancestor of the changes it induces. The prior implementation descended the nesting of its origin map. Here a node's recorded origin need not enclose its children: a function's lambda records its parameter. A snapshot therefore spans each node by its extent, the hull of its own origin and its children's extents, which nests by construction. The descent examines the children of the enclosing nodes alone, level by level, so its work follows the locus's depth; it keeps every enclosing sibling rather than the first, which keeps it exact where a point touches two siblings. A linear scan of every node is its oracle. The extent step retires if the lowering's origins come to nest, when each extent equals its origin.

## The parse's repairs ride beside the step

`Submission::obligations` carries the completion obligations the parse recorded — each repair's class and the bytes held responsible — on both paths, a revision judged and one refused whole. The step a face renders holds the composition, which keeps no trace of the repairs, so the submission takes them from the lowering before consuming it. The parse orders them by severity, the order its minimization folds; the submission orders them by span, the order a reader meets them, equal spans keeping the parse's order. The rows are the revision's: a clean revision after a recovering one carries none.

The recorded design is the prior implementation's: the lowering carried the parse's buffer verbatim, and the report projected it into source-ordered rows of a published vocabulary, which a render bus turned into cards and a JSON report serialized. Here the rows are the parser's own `ObligationInstance`s, since no face reads a published vocabulary yet; the vocabulary, the cards and the codec arrive with the first face that consumes them. The alternative was to add the obligations to the dispatcher's step, which every batch verb would then carry unread. The choice reverses when the step itself carries the parse's obligations; the submission then forwards the step's.

## Diagnostics and goals are the renderer's

A submission's diagnostics are the reports `gandr-surface-diagnostics` renders from its step under the verb a face runs: a refusal at its own locus, an unsettled declaration, and under `check --goals` a goal. A goal is a declaration owed its body — a signature with no definition — which the checker answers with the hole rule and the incremental checker marks as a hole in the item's footprint; the goals suite checks that the two predicates agree item by item.

The prior implementation's goals were holes inside bodies, each with its expected type and local context, and it recovered a malformed declaration as such a hole. The surface has no hole term yet, so the goals here stand for whole bodies and goals over sub-term holes arrive with the hole surface; a malformed declaration is refused in place, its report the refusal at the responsible bytes, and the declarations after it lower intact. The prior attribute pass reported an ill-typed payload as the checker's type error; here the lowering types a payload against its schema where it reads it, and refuses a mismatch as `IllTypedPayload`, in the malformed-source class every type error takes.

## Tests: the floor, the deferred rows, the defects

The prior implementation's session, incremental, edit, diagnostics and goals suites, with the tests beside their source, are the floor: 162 tests. A row over a former the fragment does not have is deferred by name with that former.

| Suite | Floor | Here | Deferred |
| ----- | ----- | ---- | -------- |
| session, beside the source | 9 | 3 | 6 |
| session | 42 | 9 | 33 |
| incremental | 13 | 9 | 4 |
| edit, beside the source | 3 | 3 | 0 |
| edit | 52 | 14 | 38 |
| edit, extra | 3 | 0 | 3 |
| diagnostics | 14 | 5 | 9 |
| diagnostics, attributes | 5 | 5 | 0 |
| diagnostics, frames | 2 | 0 | 2 |
| diagnostics, obligations | 15 | 8 | 7 |
| goals, extra | 3 | 0 | 3 |
| goals, beside the source | 1 | 1 | 0 |
| total | 162 | 57 | 105 |

The ported rows keep their names. A row whose prior form also evaluated its item keeps its typing half here; evaluation is deferred with the machine. `scalar_literals_carry_their_types` covers integer and string literals; the suffixed numeric literal is outside the fragment. The incremental property `incremental_equals_from_scratch` runs a chain of one to four edits per case, 200 cases, over revisions of one to six statements from a pool of six names with integer, string, reference, thunk, function-applying thunk, function-tail and signature-only bodies and `Integer`, `String` and `U (F Integer)` signatures, under replace, insert, delete, coordinated rename, swap, ascribe and value-only edits; each step's report must equal the dispatcher's and its typings the checker's module entry.

The edit rows take the fragment's formers. `literal_edit_is_one_set_int` and the localization rows run over the incremental fixture pair, `item_insertion_leaves_neighbours_untouched` over the stale-relocation pair rewritten without operators; the changed former of `constructor_change_is_one_replace` is a literal becoming a thunk, of `comp_constructor_change_is_one_replace` a return becoming an application; `hole_fill_and_erase` fills and erases an owed declaration's body; `multi_point_edit_localizes_to_the_common_ancestor` changes a callee and its argument. `step_comp_child_order_matches_diff_and_rebuild` pins the child order over a hand-built arena holding the core's multi-child formers — `case`, bind, application, pair — since the effect formers it was written over are absent. The properties `apply_of_diff_reproduces_new` and `self_diff_is_identity` run 200 cases each over the incremental generator's revisions.

The diagnostics rows submit each source to a fresh session and read the reports its step renders. The error corpus holds one row per refusal a declaration of the fragment reaches, the checker's shape mismatch once per former its rules require, and the lowering's refusal of a source as a whole; `error_corpus_reports_match_goldens` and `goal_corpus_reports_match_goldens` pin the rendered text under `tests/golden/`, where the prior goldens were JSON reports. `repeated_equal_subterms_point_to_the_failing_occurrence` writes its equal literals in two declarations, since tuples and ascription are outside the fragment. The attribute rows take the registry's `owes` and `refuses` where the prior rows took `doc`. `goal_flags_match_checkpoint_footprints_for_recovery_fixtures` runs over the `parser-recovery` and `incomplete-input` fixtures rewritten into the fragment: the prior sources, a shell block and a top-level expression, are refused whole here and would offer no item to compare.

Deferred, with the former each needs:

- Path types and definitional unfolding: `a_definition_reaches_the_typing_context_chain`, `a_law_over_a_definition_types_from_source`, `a_law_over_a_definition_types_when_both_arrive_in_one_source`, `a_law_over_a_definition_that_returns_otherwise_is_refused`.
- Graded thunk types: `a_graded_bridge_signature_is_an_abstention_not_a_refusal`.
- Dependent binders at the surface: `a_dependent_signature_is_an_abstention_not_a_refusal`.
- Sum types and `case`: `one_part_case_bodied_function_checks_and_evaluates`, `erased_sum_definition_is_consumed_by_a_later_case`, `case_arm_rename_targets_the_right_slot`, `case_second_arm_rename_targets_the_snd_slot`, `case_both_arms_renamed_at_once`, `case_scrutinee_edit_descends_to_one_set_int`.
- Injections at the surface: `injection_side_flip_is_one_set_side`.
- Pair elimination: `split_first_binder_rename_targets_the_fst_slot`, `split_second_binder_rename_targets_the_snd_slot`, `split_both_binders_renamed_at_once`, `split_scrutinee_edit_descends_to_one_set_int`.
- Lazy products, their projections and computation holes: `projection_side_flip_is_one_set_side`, `projection_target_edit_descends_to_one_set_int`, `with_field_edit_is_one_set_int`, `with_second_field_edit_is_one_set_int`, `a_vanishing_or_appearing_computation_hole_is_erase_or_fill`.
- Grades: `grade_bump_is_one_set_grade`, `attribute_and_nested_child_edit_compose`, `grade_op_value_edits_localize`.
- Named binders, which the core's de Bruijn indices do not keep: `binder_rename_composes_rebind_and_setvar`.
- Annotations: `value_ascription_change_is_one_set_annotation`, `binder_annotation_added_is_one_set_annotation`, `binder_annotation_dropped_is_one_set_annotation`.
- A computation-rooted declaration body: `cross_sort_root_replace_is_reconstructed`.
- Effects, handlers and delimited control: `resume_computation_edit_localizes`, `reified_stack_is_opaque_but_sound`, `handle_scrutinee_edit_localizes`, `handle_return_body_edit_localizes`, `perform_op_change_is_replace`, `handle_skeleton_change_is_replace`, `shift_binder_rebind_and_body_edit_compose`, `handle_skeleton_dimensions_are_replace`, `handle_clause_body_edit_localizes`, `resume_stack_edit_localizes`, `cross_constructor_change_is_replace`, `perform_signature_change_is_replace`, `perform_payload_edit_localizes`, `reset_body_edit_localizes`, `handle_second_clause_body_edit_localizes`, `handle_body_edits_round_trip`, `effect_control_pairs_round_trip`.
- Evaluation: `integer_literal_types_and_evaluates`, `nullary_function_call_evaluates`, `holes_decline_evaluation` (with typed holes).
- The unknown type, absent by construction: `computation_top_result_types_binds_and_applies`, `value_unknown_ascription_types_and_evaluates`.
- Operators and the builtin prelude: `arithmetic_operators_type_check_and_evaluate`, `operator_definition_carries_across_lines`, `module_builtins_type_and_evaluate`, `comparison_operators_type_check_and_evaluate`, `boolean_operators_type_check_and_evaluate`, `string_builtin_type_and_evaluate`, `string_contains_scans_conflict_marker_text`, `rung07_builtins_type_check_and_evaluate`, `rung07_builtin_failures_are_gradual_blame`, `rung07_wrong_shape_calls_are_static_type_errors`, `regex_builtin_type_and_evaluate`, `regex_extract_failures_are_gradual_blame`, `an_unknown_prelude_member_is_declined_as_a_hole`.
- Lists: `list_concat_type_checks_and_evaluates`, `lists_need_an_annotation_then_evaluate`, `list_each_maps_a_closure_over_a_list`, `list_reduce_folds_a_list`, `list_functional_update_builtins_evaluate`, `out_of_bounds_list_update_blames`, `list_any_and_sort_evaluate`, `list_where_filters_by_a_predicate`.
- Records: `record_get_and_insert_evaluate`, `record_update_rebuilds_a_fresh_record`.
- Lists and records together: `same_shape_containers_descend_and_apply_rebuilds_them`, `shape_changes_replace_wholesale_and_apply_installs_the_subtree`.
- Computation ascription in expression position: `computation_ascription_types_and_evaluates_check_only_forms`.
- Foreign declarations: `extern_declaration_carries_across_lines_and_a_foreign_call_blames_without_a_handler`.
- Module declarations: `a_hidden_or_absent_user_module_component_is_declined_as_a_hole`, `a_whole_file_submission_reports_the_missing_module_component_goal`.
- Typed holes in `case` patterns: `filling_a_pattern_hole_resumes_to_the_written_source`, `opening_a_pattern_hole_resumes_to_the_unfinished_source`, `filling_a_hole_invalidates_only_the_item_holding_it`, `a_type_stable_fill_adopts_its_dependent`.
- A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them: `every_parser_class_maps_to_its_own_name_and_rank`, `cards_preserve_the_report_rows`, `a_clean_source_produces_no_cards`, `advertised_capabilities_match_the_live_path`, `report_json_carries_the_rows_and_round_trips`, `an_empty_row_set_serializes_as_an_empty_array`, `a_render_frame_round_trips_the_produced_cards`, `spans_are_in_source_and_schema_is_versioned`, `reports_round_trip_through_json`.
- Semantic marks, the checker's pass marking each typed node: `corpus_covers_each_reachable_mark_kind`, `oracle_error_marks_iff_ill_typed`, `is_error_classifies_empty_hole_only`, `mark_spans_lie_in_source`, `no_surface_source_yields_effect_or_other_mark`, `surface_marks_are_never_dropped`, `catch_all_and_effect_row_mark_shapes_round_trip` (with effect rows and the JSON codec).
- Checker failure frames, the structural context a nested refusal is reported within: `each_checker_frame_localizes_its_nested_failure`, `binder_naming_frames_carry_their_binder`.
- A declaration of computation type, which the lowering refuses as out of fragment: `a_computation_signature_folds_into_its_def_and_yields_one_hole_goal` (with a hole term), `a_computation_signature_on_a_hole_free_body_types_through_the_check_entry`.

Two defects of the prior implementation are absent. A submission panicked on a corpus source the walk passed: absent at L2, since `tests::corpus::every_source_submits_as_the_walk_composes_it` submits every source of both roots whole and compares each with the walk's step. Total lowering accepted wrong programs through the unknown type: absent by construction, since no unknown former exists.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
