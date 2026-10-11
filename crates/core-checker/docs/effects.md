# Effects and control

How `gandr-core-checker` checks effect rows, operation requests, deep handlers, first-class stacks, resumptions and delimited control. The crate's [README](../README.md) states the rest of the crate; `gandr-core-term`'s [README](../../core-term/README.md#effect-rows) states the syntax and the row laws.

<!-- toc -->
- [The rules](#the-rules)
- [Variance](#variance)
- [The unknown type](#the-unknown-type)
- [The decision](#the-decision)
- [Witnesses](#witnesses)
- [Floor](#floor)
<!-- tocstop -->

## The rules

A perform checks its payload and synthesises its reply under its singleton interface row. A handler covers that interface exactly once and checks every branch against its answer, retaining residual effects. Shared interface names require invariant operation types. Effectful bind needs a returner continuation; pure bind may continue with a lambda.

Stack Apply instantiates a dependent codomain; Bind unions rows and strengthens its result, refusing escaping type codes as `DependentStack`; Project selects a lazy-pair component. Reset supplies Shift's answer, weakened through intervening binders. Stack literals, handlers, resets, shifts and lazy pairs check rather than synthesise. A handler's subject and a Bind frame's body synthesise, so a bare `return` there is refused as a checking form.

## Variance

A returner's row is covariant: `F A` stands where `F^ε A` is expected, never the reverse. Operation payload and reply types are invariant. A stack `Stack(B, C)` is contravariant in what it consumes and covariant in what it delivers: it stands where `Stack(B′, C′)` is expected when `B′ ⊑ B` and `C ⊑ C′`.

## The unknown type

Against the unknown type, a stack literal runs its frames over unknown endpoints, a lazy pair checks both components against unknowns, and a List reads an unknown element. A handler checked against the unknown answer reads it through the matched returner: the residual is absorbed and each resumption consumes the reply under the empty row. A resumption of a hole infers the unknown type, so a hole in stack position stays local.

## The decision

**Choice.** Keep bidirectional rules and named refusals, not answer-type inference or a row solver. **Reversal.** Revisit for an explicit answer-polymorphic contract. Control formers and nonempty rows never become assumed declarations at pure readmission.

## Witnesses

In `judgement::tests`: `pure_bind_into_lambda_is_unchanged`, `effectful_bind_into_lambda_is_shape_mismatch`, `bind_unions_effect_rows`, `check_mode_bind_subsumes_the_accumulated_row`, `check_mode_bind_accepts_a_contained_row`, `host_operations_check_payloads_and_retain_effects`, `handlers_discharge_only_their_own_interface`, `handle_against_a_non_returner_is_stuck`, `handle_of_a_non_returner_scrutinee_is_a_shape_mismatch`, `empty_signature_handler_finishes_after_the_return_clause`, `handle_against_unknown_answer`, `control_rules_preserve_rows_scopes_and_shapes`, `reset_answers_are_weakened_through_intervening_binders`, `a_stack_bind_cannot_export_its_local_type_code`, `stack_bind_accumulates_input_and_body_rows`, `reify_empty_stack_is_identity`, `reify_delivered_answer_subsumes_up`, `reify_delivered_answer_cannot_drop_a_row`, `reify_against_non_stack_type_is_stuck`, `reify_interior_bind_frame_threads_the_accumulated_row`, `resume_of_a_non_stack_is_a_shape_mismatch`, `resume_delivering_a_row_cannot_drop_it`, `resume_delivered_answer_subsumes_up`, `resume_of_a_hole_infers_unknown`, `reset_is_transparent_on_the_type`, `shift_binds_the_continuation_at_the_captured_type` and `an_introduction_against_the_unknown_type_checks_its_parts`.

In `conversion::tests`: `returner_rows_are_covariant_but_signature_types_are_invariant`, `stack_is_contravariant_in_b_covariant_in_c_positive` and `stack_variance_negative`. In `formation::tests`: `effect_operation_types_participate_in_formation_levels_and_scope`. Export: `bridge::tests::effectful_declarations_are_refused_by_name_at_the_pure_boundary`.

## Floor

The prior implementation's 47 effect and control conformance rows, by name. Twenty-two run here under their own name. The other twenty-five name the consolidated test that asserts the same judgement; none is deferred.

| Prior row | Witness here |
| --------- | ------------ |
| `perform_infers_singleton_row` | `judgement::tests::host_operations_check_payloads_and_retain_effects` |
| `perform_payload_is_checked` | `judgement::tests::host_operations_check_payloads_and_retain_effects` |
| `perform_unknown_op_is_stuck` | `judgement::tests::host_operations_check_payloads_and_retain_effects` |
| `bind_unions_effect_rows` | by name |
| `pure_bind_into_lambda_is_unchanged` | by name |
| `effectful_bind_into_lambda_is_shape_mismatch` | by name |
| `check_mode_bind_subsumes_the_accumulated_row` | by name |
| `check_mode_bind_accepts_a_contained_row` | by name |
| `handle_discharges_a_signature` | `judgement::tests::handlers_discharge_only_their_own_interface` |
| `handle_leaking_an_unhandled_effect_is_a_type_mismatch` | `judgement::tests::handlers_discharge_only_their_own_interface` |
| `handle_in_inference_is_stuck` | `judgement::tests::handlers_discharge_only_their_own_interface` |
| `handler_coverage_must_be_exact` | `judgement::tests::handlers_discharge_only_their_own_interface` |
| `handle_clause_cannot_launder_an_effect_through_a_bind` | `judgement::tests::handlers_discharge_only_their_own_interface` |
| `handle_against_a_non_returner_is_stuck` | by name |
| `handle_of_a_non_returner_scrutinee_is_a_shape_mismatch` | by name |
| `empty_signature_handler_finishes_after_the_return_clause` | by name |
| `handle_against_unknown_answer` | by name |
| `returner_row_is_subset_widened_positive` | `conversion::tests::returner_rows_are_covariant_but_signature_types_are_invariant` |
| `returner_row_is_subset_widened_negative` | `conversion::tests::returner_rows_are_covariant_but_signature_types_are_invariant` |
| `stack_is_contravariant_in_b_covariant_in_c_positive` | by name |
| `stack_variance_negative` | by name |
| `reify_empty_stack_is_identity` | by name |
| `reify_delivered_answer_subsumes_up` | by name |
| `reify_delivered_answer_cannot_drop_a_row` | by name |
| `reify_argument_frame` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `reify_projection_frame` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `reify_bind_frame_carries_the_continuation_row` | `judgement::tests::stack_bind_accumulates_input_and_body_rows` |
| `reify_bind_frame_folds_the_consumed_row` | `judgement::tests::stack_bind_accumulates_input_and_body_rows` |
| `reify_bind_frame_cannot_launder_its_row` | `judgement::tests::stack_bind_accumulates_input_and_body_rows` |
| `reify_interior_bind_frame_threads_the_accumulated_row` | by name |
| `reify_in_inference_is_stuck` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `reify_against_non_stack_type_is_stuck` | by name |
| `reify_against_unknown_is_the_matched_stack` | `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts` |
| `resume_infers_the_delivered_answer` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `resume_checks_the_fed_computation` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `resume_of_a_non_stack_is_a_shape_mismatch` | by name |
| `resume_delivering_a_row_cannot_drop_it` | by name |
| `resume_delivered_answer_subsumes_up` | by name |
| `resume_of_a_hole_infers_unknown` | by name |
| `reset_is_transparent_on_the_type` | by name |
| `reset_in_inference_is_stuck` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `reset_shift_resume_round_trip` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `reset_returns_the_matched_body_type_not_the_answer` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `shift_binds_the_continuation_at_the_captured_type` | by name |
| `shift_outside_reset_is_stuck` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `shift_in_inference_is_stuck` | `judgement::tests::control_rules_preserve_rows_scopes_and_shapes` |
| `effects_control_class_rejects_exactly` | `bridge::tests::effectful_declarations_are_refused_by_name_at_the_pure_boundary` |
