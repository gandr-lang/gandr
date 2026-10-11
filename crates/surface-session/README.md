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
- [The kernel checkpoint](#the-kernel-checkpoint)
- [The import scope persists across submissions](#the-import-scope-persists-across-submissions)
- [Edits are a diff of the lowered core](#edits-are-a-diff-of-the-lowered-core)
- [Native declaration snapshots](#native-declaration-snapshots)
- [Native universe-path content](#native-universe-path-content)
- [Localization descends extents](#localization-descends-extents)
- [The parse's repairs ride beside the step](#the-parses-repairs-ride-beside-the-step)
- [Diagnostics and goals are the renderer's](#diagnostics-and-goals-are-the-renderers)
- [A hole-free item is evaluated](#a-hole-free-item-is-evaluated)
- [Contract evidence and its limits](#contract-evidence-and-its-limits)
- [Deferred behavioral floor](#deferred-behavioral-floor)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Session` takes successive revisions of one source through `Session::submit`. Each revision is lowered once; the dispatcher's `judge_module` judges, readmits and settles the lowered module, and the same declarations, offered by the item source as a `Program`, go to the incremental checker, which adopts every checkpoint that still answers, judges the rest and persists the set. The composition's kernel artifact — what the readmission let cross — is committed into a block store as records through `gandr-storage-artifact`. The `Submission` carries the dispatcher's `Composed` and `Standing` for the text, the resume's census and whether the checkpoints were stored, the manifest of the kernel checkpoint, the edit actions from the latest accepted revision and the parse's completion obligations, and turns into the dispatcher's `Step` so a face renders it through the same renderer the batch verbs use. `Session::reopen` restores a session over the checkpoints an earlier one wrote, and `Session::read_kernel` reads a kernel checkpoint back through the kernel's decoder.

**Why.** The REPL, the language server and a terminal interface all need what the batch pipeline does not keep: the latest resume to adopt from, a checkpoint store that outlives the process, and the import scope of the last revision that lowered. Holding that state once, below every face, means each face is a loop over `submit` and a renderer of steps, and every face's verdicts are the batch pipeline's.

**How.** `submit` calls the dispatcher's `lower_source`, then `judge_module` for the report and `program` plus `IncrementalSession::submit` for the resume, over a copy of the lowered arena. A whole-revision refusal is `Composed::Refused`: it retains the accepted resume, imports, and snapshot but advances the lowering-attempt count. Checkpoints use `CheckpointStore`; a store failure becomes `Persistence::Failed` when a resume remains available, otherwise `SessionFault::Store`. A kernel block-store refusal is carried as `KernelCheckpoint::Failed` without discarding the accepted resume.

## References

- Microsoft. "Language Server Protocol Specification, version 3.17." 2022. <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — full-document synchronisation, the shape a submission takes: the client owns the buffer and sends it whole.
- Porter et al. "Incremental Bidirectional Typing via Order Maintenance." arXiv:2504.08946, 2025. <https://arxiv.org/abs/2504.08946> — an incremental checker that consumes structured edit actions rather than text, the input edit reconstruction produces.
- Hunt, J. W., and Szymanski, T. G. "A Fast Algorithm for Computing Longest Common Subsequences." Communications of the ACM 20(5), 1977. — the reduction of a longest common subsequence over distinct keys to a longest increasing subsequence, which item alignment uses.

## Provided features

- **The session.** `Session`, `Session::new`, `Session::submit`, `Session::last`, `Session::stream`, `Session::lowerings`, `Session::into_store`; `Submission`, `Resumed`, `Persistence`, `resumed::Absent`, `SessionFault`. Witnesses: `tests::corpus::every_source_submits_as_the_walk_composes_it`, `tests::session::whole_file_submit_carries_definitions_forward`, `tests::session::successful_submissions_publish_whole_program_synthesis`, `tests::session::failed_submission_retains_latest_synthesis`.
- **The step a face renders.** `Submission::into_step`: the submission as the dispatcher's `Step::Source`. Witnesses: `tests::corpus::every_source_submits_as_the_walk_composes_it`, and the diagnostic suites' stable refusal identifiers and exact source loci; English titles and rendered report layout are not contracts.
- **The parser's repairs.** `Submission::obligations`: the parse's completion obligations, in source order. Witnesses: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`, `tests::diag_obligations::rows_are_in_source_order_not_severity_order`, `tests::diag_obligations::a_clean_source_reports_no_obligations`.
- **Checkpoints across processes.** `Session::reopen`, `Reopened`, `reopened::Absent`. Witnesses: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`, `tests::checkpoint::a_store_holding_nothing_reopens_fresh`, `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`.
- **The kernel checkpoint.** `KernelCheckpoint`, `Submission::kernel`, `Session::read_kernel`, `Session::blocks`. Witnesses: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`, `tests::checkpoint::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`, `tests::corpus::every_source_submits_as_the_walk_composes_it`.
- **The import scope.** `Session::resolve_import`, `ImportRow`, `import::Absent`. Witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`.
- **The item source.** `program`, `SurfaceItems` (an `ItemSource`), `Revision`, `RevisionFault`, `fault_span::Absent`. Witnesses: `tests::items::each_unrefused_declaration_is_one_item_keyed_by_its_name`, `tests::items::the_item_source_offers_a_revision_or_names_its_fault`.
- **Evaluation.** `Submission::evaluate`, `evaluate`, `evaluation::Absent`: a hole-free item run on the dispatcher's run stage. Witnesses: `tests::session::integer_literal_types_and_evaluates`, `tests::session::nullary_function_call_evaluates`, `tests::session::holes_decline_evaluation`.
- **Edit-action reconstruction.** `Snapshot` (`of`, `items`, `node`, `span`, `localize`, `edit_locus`), `diff`, `apply`, `EditScript`, `Action`, `CorePath`, `ChildSlot`, `Tree`, `ItemTree`, `SourceEdit`, the reasons `addressed`, `spanned`, `located` and `body_path`; `Submission::edits`, `Session::snapshot`. Witnesses: `tests::edit::apply_of_diff_reproduces_new`, `tests::edit::literal_edit_is_one_set_int`, `tests::edit::multi_point_edit_localizes_to_the_common_ancestor`, `tests::edit::a_submission_carries_the_edits_from_the_last_accepted_revision`, `edit::tests::descent_agrees_with_the_linear_stab_oracle`.

## Expected features

- **A checkpoint store.** Any `CheckpointStore`: `gandr-core-incremental`'s `MemoryCheckpointStore` for a session that dies with its process, its `FileCheckpointStore` for one that outlives it.
- **A block store.** Any `BlockStore`: `gandr-storage-records`' `InMemoryBlockStore` for a session that dies with its process; a store that outlives it carries the kernel checkpoints to the next.
- **A backend identity.** A `BackendArtifact` naming the checker build, so checkpoints a different checker judged are never restored.
- **The text.** The caller owns the source's buffer and submits each revision whole; the submission borrows it.
- **A renderer.** `gandr-surface-diagnostics` renders the `Step` a submission turns into.

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

A declaration the lowering refuses is reported as refused and offered to no one; a declaration the checker refuses is reported as refused and resumed as `Typing::Refused`. A whole-revision lowering refusal retains the accepted state while recording another lowering attempt. A fault — a tree the parser cannot commit, a lowering or kernel disagreement — is a `SessionFault`, never a verdict about the source. There is no unknown former that could turn an unlowerable term into an accepted one.

## The item source

`program` keys each declaration the lowering did not refuse by its name as written and carries exactly the declaration the dispatcher's `adapt` gives the checker, in admission order; refused declarations are left out and the admission positions skip them. The incremental checker therefore resumes over the declarations the batch judgement checks and no other. `SurfaceItems` is the same lowering behind `gandr-core-incremental`'s `ItemSource`; because that seam's error cannot borrow the revision, a whole-revision refusal crosses it as its failure class and span.

## Checkpoints

Every accepted submission attempts to persist its checkpoints under its program's content address. A failed write need not leave an external store unchanged. If the incremental session retains a resume, the submission reports `Persistence::Failed` and the next submission can adopt from it; otherwise the failure is `SessionFault::Store`. `Session::reopen` lowers its supplied revision and restores checkpoints for that program and backend. An absent or incompatible checkpoint set reopens fresh and says why. A restored set is not trusted: the next resume validates each checkpoint as it validates an in-memory one.

## The kernel checkpoint

**Choice.** Every accepted submission commits the composition's kernel artifact into the session's block store through `gandr-storage-artifact`: one record per declaration segment, cut where the kernel's decoder ends each, under a manifest whose identity binds the record plane's boundary commitment, the record count, the root node and the kernel format version. The submission carries the manifest, and the caller keeps it as it keeps anything — `ArtifactManifest::encode` gives its bytes. `Session::read_kernel` is the one way back: it refuses a manifest of another profile or kernel format before loading anything, re-seals the stored tree against the manifest, checks every key and cut, and hands the bytes to the kernel's bounded decoder. A matching identity says which bytes these are, never that the kernel admits them, so a manifest minted over bytes the kernel refuses names a tree the store holds and seals, and is still refused.

**Alternatives.** The encoded artifact as one opaque blob beside the checkpoints would leave no record grain, so a reader could not take one declaration's segment with its proof, and the blob would be trusted by its hash. Keying it into the `CheckpointStore` under the program's address would give that store a second kind of value its trait does not name. Restoring it in `Session::reopen` needs a manifest to read by, and the manifest is the caller's root of trust, not the session's.

**Reversal.** A durable table of manifests by program address, owned by the session, lets `Session::reopen` restore the kernel checkpoint itself; and a face that never reads the kernel environment, measured paying for the commit, moves it behind a choice the caller makes.

## The import scope persists across submissions

The session keeps the import rows and alias scope of the last revision the lowering read, owned so they outlive its text. A revision the lowering refuses — one that declares an alias twice among them — leaves the scope of the revision before it, so a face resolving `parse` keeps its answer while the author repairs the collision.

## Edits are a diff of the lowered core

Each accepted submission carries the `EditScript` from the latest accepted revision: the `diff` of their `Snapshot`s. A snapshot retains each item's `DeclarationTree`: value signature and body roots, or a complete native data signature. Each root reads out of the arena as a `Tree` of the incremental checker's `ContentNode`s, numbered breadth-first, each constant read as the `Reference` it resolves to, so two revisions lowered into two arenas compare node by node. Items align by reference — key and occurrence — keeping the largest set whose order both revisions share; each kept pair's bodies are walked together, a changed literal, variable or constant becoming one in-place action and any other change one `Replace` of the old subtree. `apply` of a diff to the old items reproduces the new ones exactly: soundness is total, localization is partial. A path names an item and the child slots from its body's root; an action anchored in the old revision carries the old ordinal, an insertion the new one.

The recorded design is this contract over the prior implementation's named surface core, with actions for grades, injection sides, binder names and annotations, and items aligned by a longest common subsequence of their names in an `n·m` table. The core here carries none of those payloads — binders are de Bruijn indices, so renaming one reconstructs to no action — and its actions are the core's own leaves. Because references are unique within a revision, the longest common subsequence is the longest increasing run of matched old ordinals, which patience sorting finds in `n log n`. The alternatives were a text diff, which names bytes rather than terms, and a diff of content-addressed tables, which numbers nodes and loses the path a face surfaces. The choice reverses when the lowering emits structured edits itself; the session would then forward them.

## Native declaration snapshots

`DeclarationTree::Value` and `DeclarationTree::Data` preserve distinct declaration categories. Data snapshots retain their kind, parameter telescope and every constructor field. A schema or category change replaces the item through delete/insert; native term children still receive localized edits. Record labels, constructor tags, nominal identities and all variadic children participate in agreement. The child reader is an unbounded borrowed iterator, not a fixed three-child buffer.

`edit::native_snapshots_preserve_schema_and_fourth_children` checks literal edits beneath fourth nominal arguments, constructor fields, case branches and record fields, plus schema and category replacements; applying each diff reconstructs the exact new snapshot. Native declarations have no runtime body: evaluation returns `UnrunnableData`. No source notation or command-IL implementation is inferred from retaining this programmatic content.

**Choice.** Extend the existing snapshot and diff contract rather than maintain a second nominal identity table. **Reversal.** A source reader or runtime consumer must add its own syntax and execution rules before these native items become runnable from the session.

## Native universe-path content

Edit snapshots retain native `Path_U` classifiers, reflexivity, equivalence maps and evidence, product paths, and transport operands as the incremental layer’s content nodes. Their child ordering is the ordinary constructor ordering. Both ordered dialogue lists participate in non-child payload agreement: an evidence-only change produces a replacement even when every child is unchanged. The witness `edit::tests::path_evidence_changes_are_reconstructed` observes source- and target-dialogue changes separately, exact reader child order, and replay of the new content. Evidence-insensitive certificate conversion is not content equality. No session revision becomes a certificate admission receipt by retaining this content.

**Choice.** Extend the existing structural edit vocabulary rather than maintain a second path identity table. These forms are programmatic core content; source-level identity operations, bridge-mode observations, higher fields, funext, `Flow_U` and guarded List values are not introduced by this adapter. **Reversal.** An interactive identity consumer must define its own application and persistence boundary over the kernel APIs.

## Localization descends extents

`Snapshot::localize` returns the body node whose span encloses a range with the fewest bytes, the outermost of a shared span and the leftmost at one depth — the prior implementation's rule, so a contiguous edit's locus is the common ancestor of the changes it induces. The prior implementation descended the nesting of its origin map. Here a node's recorded origin need not enclose its children: a function's lambda records its parameter. A snapshot therefore spans each node by its extent, the hull of its own origin and its children's extents, which nests by construction. The descent examines the children of the enclosing nodes alone, level by level, so its work follows the locus's depth; it keeps every enclosing sibling rather than the first, which keeps it exact where a point touches two siblings. A linear scan of every node is its oracle. The extent step retires if the lowering's origins come to nest, when each extent equals its origin.

## The parse's repairs ride beside the step

`Submission::obligations` carries the completion obligations the parse recorded — each repair's class and the bytes held responsible — on both paths, a revision judged and one refused whole. The step a face renders holds the composition, which keeps no trace of the repairs, so the submission takes them from the lowering before consuming it. The parse orders them by severity, the order its minimization folds; the submission orders them by span, the order a reader meets them, equal spans keeping the parse's order. The rows are the revision's: a clean revision after a recovering one carries none.

The recorded design is the prior implementation's: the lowering carried the parse's buffer verbatim, and the report projected it into source-ordered rows of a published vocabulary, which a render bus turned into cards and a JSON report serialized. Here the rows are the parser's own `ObligationInstance`s, since no face reads a published vocabulary yet; the vocabulary, the cards and the codec arrive with the first face that consumes them. The alternative was to add the obligations to the dispatcher's step, which every batch verb would then carry unread. The choice reverses when the step itself carries the parse's obligations; the submission then forwards the step's.

## Diagnostics and goals are the renderer's

A submission's diagnostics are the reports `gandr-surface-diagnostics` renders from its step under the verb a face runs: a refusal at its own locus, an unsettled declaration, and under `check --goals` a goal. A goal is a declaration owed its body — a signature with no definition — which the checker answers with the hole rule and the incremental checker marks as a hole in the item's footprint; the goals suite checks that the two predicates agree item by item.

The prior implementation's goals were holes inside bodies, each with its expected type and local context, and it recovered a malformed declaration as such a hole. The surface has no hole term yet, so the goals here stand for whole bodies and goals over sub-term holes arrive with the hole surface; a malformed declaration is refused in place, its report the refusal at the responsible bytes, and the declarations after it lower intact. The prior attribute pass reported an ill-typed payload as the checker's type error; here the lowering types a payload against its schema where it reads it, and refuses a mismatch as `IllTypedPayload`, in the malformed-source class every type error takes.

## A hole-free item is evaluated

`Submission::evaluate` runs one declaration of the revision on the `Program` the dispatcher's composition built, the same run `gandr run` makes, and returns what it came to. The rule is `evaluate`, over a declaration and its program, so a face holding the submission's step applies it without the submission: a declaration the checker accepted — checked or synthesised — runs; one owed its body is a hole and declines with `evaluation::Absent::Holed`; one refused by the lowering, the checker or its root declines with `evaluation::Absent::Unaccepted`, as does a position holding no declaration and a revision refused whole. A declaration that runs into a goal elsewhere is not a hole of its own: it runs, and the run is blamed on the goal. Each evaluation is a fresh machine, so evaluating twice runs twice and nothing is cached between revisions. A native data declaration is not a runtime value and returns `evaluation::Absent::DataUnrunnable`.

The prior implementation evaluated a top-level expression and reported a definition with its type alone. The fragment has no top-level expression, so the item evaluated is a declaration, and the loop prints a value line under each checked one. The alternative was evaluating nothing until expressions exist, which leaves the loop unable to show a value. The choice reverses when the surface gains a top-level expression: that item is the one evaluated, and a definition returns to its type line alone.

## Contract evidence and its limits

Nontrivial callable items carry executable `#[spec(...)]` predicates and bounded adequacy witnesses. The predicates observe existing state: ordered rows, preserved payloads, exact absence reasons, source bounds, canonical tree numbering, and session transitions. They do not repeat parsing, callback invocation, evaluation, or storage effects. The private child iterator exposes its borrowed position to its predicates; `DeclarationTree` makes native declaration categories explicit in the snapshot API.

Declarations with no callable boundary, opaque strategy constructors, formatter sinks, best-effort cleanup, and the consumed-input differential helper state precise executable exemptions. Their observable obligations are exercised where the inputs and effects exist. Every exemption names that boundary rather than treating a non-const comparison as an exemption.

| Decision surface | Evidence and bounded domain | Rung |
| ---------------- | --------------------------- | ---- |
| Incremental reuse | Literal adoption and retyping fixtures, plus 200 generated edit chains; complete typings compared with a fresh checker. | L2 |
| Corpus composition | Every source from both configured corpus roots compared with the walk; both paths share parsing and judgement. | L3 |
| Edit reconstruction | Literal actions, 200 generated revision pairs, and a hand-built dynamic tree; applying the diff reconstructs the new image. | L3 |
| Item alignment | All subset/permutation pairs of three references compared with exhaustive reference subsequences. | L2 |
| Localization | Descent compared with a linear span oracle on generated trees, including ties; visited-node bounds cover the measured shapes only. | L2 |
| Arena and origin boundaries | Missing item/body/child, unrecorded spans, absent roots of each sort, descendant hulls, and callback-once fixtures. | L3 |
| Session and evaluation | Exact report rows, import retention, attempt counts, missing/refused/holed eligibility, and concrete integer/thunk results. | L3 |
| Persistence and formatting | Real file-store reopen/cleanup, kernel readback, refusing checkpoint/block stores, and refusing output sinks. External failure modes beyond those fixtures are not claimed. | L3 |

Diagnostics assert stable refusal categories and exact primary/context spans, not title wording or golden report text. The obligation suites preserve repair classes, loci, multiplicities, and ordering; agreement with the same parser is transfer evidence, not an independent repair oracle. Goal flags are compared with the corresponding checkpoint footprints.

The generated source domain uses the supported scalar, declaration, reference, and nullary-function forms. Hand-built arena fixtures cover core child ordering without pretending those effect formers have surface syntax. These finite witnesses do not establish universal diff soundness, typing correctness, storage atomicity, or behavior of surface forms the grammar cannot express.

The choice is cheap executable boundary checks plus independent or literal consumer observations. Re-running the full parser, evaluator, or store in a postcondition would duplicate work and effects; opaque test strategies are not sampled a second time. An exemption can be removed when the relevant state has a non-consuming observer. Broader grammars or new decision branches require broader witnesses, not a stronger claim about the existing samples.

## Deferred behavioral floor

The named census contains **102 obligations: seven witnessed and 95 deferred**. Five are exercised here: four native-prelude witnesses enabled by [#71](https://github.com/gandr-lang/gandr/pull/71), and the dependent-signature witness enabled by [dependent lowering](https://github.com/gandr-lang/gandr/commit/1a07bbc4b487db0ad99cf61d0bacef942df94a92).

- `a_dependent_signature_is_an_abstention_not_a_refusal`
- `arithmetic_operators_type_check_and_evaluate`
- `operator_definition_carries_across_lines`
- `module_builtins_type_and_evaluate`
- `comparison_operators_type_check_and_evaluate`

`cards_preserve_the_report_rows` and `a_clean_source_produces_no_cards` are witnessed by `surface-repl::remote::tests` through [the repair-card reader](https://github.com/gandr-lang/gandr/commit/53a4804ddf4f23f1736f267e54ddb64843e387af), not duplicated here.

Core Data and record constructors do not provide source readers. The native table provides arithmetic and comparison, but not Boolean literals, string/regex/container operations or gradual-hole blame. A row remains deferred until every part of its named obligation is expressible.

| Deferred witness | Missing former or reader |
| ---------------- | ------------------------ |
| `a_definition_reaches_the_typing_context_chain` | Term-identity source reader; Path_U is a different former |
| `a_law_over_a_definition_types_from_source` | Term-identity source reader; Path_U is a different former |
| `a_law_over_a_definition_types_when_both_arrive_in_one_source` | Term-identity source reader; Path_U is a different former |
| `a_law_over_a_definition_that_returns_otherwise_is_refused` | Term-identity source reader; Path_U is a different former |
| `a_graded_bridge_signature_is_an_abstention_not_a_refusal` | Graded thunk types |
| `one_part_case_bodied_function_checks_and_evaluates` | Sum types and `case` |
| `erased_sum_definition_is_consumed_by_a_later_case` | Sum types and `case` |
| `case_arm_rename_targets_the_right_slot` | Sum types and `case` |
| `case_second_arm_rename_targets_the_snd_slot` | Sum types and `case` |
| `case_both_arms_renamed_at_once` | Sum types and `case` |
| `case_scrutinee_edit_descends_to_one_set_int` | Sum types and `case` |
| `injection_side_flip_is_one_set_side` | Injections at the surface |
| `split_first_binder_rename_targets_the_fst_slot` | Pair elimination |
| `split_second_binder_rename_targets_the_snd_slot` | Pair elimination |
| `split_both_binders_renamed_at_once` | Pair elimination |
| `split_scrutinee_edit_descends_to_one_set_int` | Pair elimination |
| `projection_side_flip_is_one_set_side` | Lazy products, their projections and computation holes |
| `projection_target_edit_descends_to_one_set_int` | Lazy products, their projections and computation holes |
| `with_field_edit_is_one_set_int` | Lazy products, their projections and computation holes |
| `with_second_field_edit_is_one_set_int` | Lazy products, their projections and computation holes |
| `a_vanishing_or_appearing_computation_hole_is_erase_or_fill` | Lazy products, their projections and computation holes |
| `grade_bump_is_one_set_grade` | Grades |
| `attribute_and_nested_child_edit_compose` | Grades |
| `grade_op_value_edits_localize` | Grades |
| `binder_rename_composes_rebind_and_setvar` | Named binders, which the core's de Bruijn indices do not keep |
| `value_ascription_change_is_one_set_annotation` | Annotations |
| `binder_annotation_added_is_one_set_annotation` | Annotations |
| `binder_annotation_dropped_is_one_set_annotation` | Annotations |
| `cross_sort_root_replace_is_reconstructed` | A computation-rooted declaration body |
| `resume_computation_edit_localizes` | Effects, handlers and delimited control |
| `reified_stack_is_opaque_but_sound` | Effects, handlers and delimited control |
| `handle_scrutinee_edit_localizes` | Effects, handlers and delimited control |
| `handle_return_body_edit_localizes` | Effects, handlers and delimited control |
| `perform_op_change_is_replace` | Effects, handlers and delimited control |
| `handle_skeleton_change_is_replace` | Effects, handlers and delimited control |
| `shift_binder_rebind_and_body_edit_compose` | Effects, handlers and delimited control |
| `handle_skeleton_dimensions_are_replace` | Effects, handlers and delimited control |
| `handle_clause_body_edit_localizes` | Effects, handlers and delimited control |
| `resume_stack_edit_localizes` | Effects, handlers and delimited control |
| `cross_constructor_change_is_replace` | Effects, handlers and delimited control |
| `perform_signature_change_is_replace` | Effects, handlers and delimited control |
| `perform_payload_edit_localizes` | Effects, handlers and delimited control |
| `reset_body_edit_localizes` | Effects, handlers and delimited control |
| `handle_second_clause_body_edit_localizes` | Effects, handlers and delimited control |
| `handle_body_edits_round_trip` | Effects, handlers and delimited control |
| `effect_control_pairs_round_trip` | Effects, handlers and delimited control |
| `computation_top_result_types_binds_and_applies` | The unknown type, absent by construction |
| `value_unknown_ascription_types_and_evaluates` | The unknown type, absent by construction |
| `boolean_operators_type_check_and_evaluate` | Boolean-literal lowering reader |
| `string_builtin_type_and_evaluate` | String-operation primitives |
| `string_contains_scans_conflict_marker_text` | String-operation primitives |
| `rung07_builtins_type_check_and_evaluate` | Container, string and regex primitive signatures |
| `rung07_builtin_failures_are_gradual_blame` | Gradual-hole native and unresolved-name reader |
| `rung07_wrong_shape_calls_are_static_type_errors` | Container, string and regex primitive signatures |
| `regex_builtin_type_and_evaluate` | Regex-operation primitives and gradual-hole failure reader |
| `regex_extract_failures_are_gradual_blame` | Regex-operation primitives and gradual-hole failure reader |
| `an_unknown_prelude_member_is_declined_as_a_hole` | Gradual-hole native and unresolved-name reader |
| `list_concat_type_checks_and_evaluates` | List-literal lowering and the named list primitive |
| `lists_need_an_annotation_then_evaluate` | List-literal and annotation lowering |
| `list_each_maps_a_closure_over_a_list` | List-literal lowering and the named list primitive |
| `list_reduce_folds_a_list` | List-literal lowering and the named list primitive |
| `list_functional_update_builtins_evaluate` | List-literal lowering and the named list primitive |
| `out_of_bounds_list_update_blames` | List-literal lowering and the named list primitive |
| `list_any_and_sort_evaluate` | List-literal lowering and the named list primitive |
| `list_where_filters_by_a_predicate` | List-literal lowering and the named list primitive |
| `record_get_and_insert_evaluate` | Record-literal lowering and record-update primitives; native core records exist in #85 |
| `record_update_rebuilds_a_fresh_record` | Record-literal lowering and record-update primitives; native core records exist in #85 |
| `same_shape_containers_descend_and_apply_rebuilds_them` | List/record literal and list-case lowering readers |
| `shape_changes_replace_wholesale_and_apply_installs_the_subtree` | List/record literal and list-case lowering readers |
| `computation_ascription_types_and_evaluates_check_only_forms` | Computation ascription in expression position |
| `extern_declaration_carries_across_lines_and_a_foreign_call_blames_without_a_handler` | Foreign declarations |
| `a_hidden_or_absent_user_module_component_is_declined_as_a_hole` | Missing-component goal reader; module declarations alone do not provide it |
| `a_whole_file_submission_reports_the_missing_module_component_goal` | Missing-component goal reader; module declarations alone do not provide it |
| `filling_a_pattern_hole_resumes_to_the_written_source` | Typed holes in `case` patterns |
| `opening_a_pattern_hole_resumes_to_the_unfinished_source` | Typed holes in `case` patterns |
| `filling_a_hole_invalidates_only_the_item_holding_it` | Typed holes in `case` patterns |
| `a_type_stable_fill_adopts_its_dependent` | Typed holes in `case` patterns |
| `every_parser_class_maps_to_its_own_name_and_rank` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `advertised_capabilities_match_the_live_path` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `report_json_carries_the_rows_and_round_trips` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `an_empty_row_set_serializes_as_an_empty_array` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `a_render_frame_round_trips_the_produced_cards` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `spans_are_in_source_and_schema_is_versioned` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `reports_round_trip_through_json` | A published obligation vocabulary, render-bus cards and capabilities, and a versioned JSON report, which arrive with the face that consumes them |
| `corpus_covers_each_reachable_mark_kind` | Semantic marks, the checker's pass marking each typed node |
| `oracle_error_marks_iff_ill_typed` | Semantic marks, the checker's pass marking each typed node |
| `is_error_classifies_empty_hole_only` | Semantic marks, the checker's pass marking each typed node |
| `mark_spans_lie_in_source` | Semantic marks, the checker's pass marking each typed node |
| `no_surface_source_yields_effect_or_other_mark` | Semantic marks, the checker's pass marking each typed node |
| `surface_marks_are_never_dropped` | Semantic marks, the checker's pass marking each typed node |
| `catch_all_and_effect_row_mark_shapes_round_trip` | Semantic marks, the checker's pass marking each typed node |
| `each_checker_frame_localizes_its_nested_failure` | Checker failure frames, the structural context a nested refusal is reported within |
| `binder_naming_frames_carry_their_binder` | Checker failure frames, the structural context a nested refusal is reported within |
| `a_computation_signature_folds_into_its_def_and_yields_one_hole_goal` | A declaration of computation type, which the lowering refuses as out of fragment |
| `a_computation_signature_on_a_hole_free_body_types_through_the_check_entry` | A declaration of computation type, which the lowering refuses as out of fragment |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
