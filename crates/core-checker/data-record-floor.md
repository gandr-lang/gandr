# Data and record parity floor

The floor has **13 ported rows and 4 deferred rows**. Checker witness names below belong to the `native_formers::native_formers` integration module; evaluator witnesses are qualified separately. A repeated witness checks the distinct obligations named by its rows. The [representation and conversion boundary](README.md#nominal-data-and-structural-records) defines this port's admitted fragment.

| Prior witness | Current witness or missing reader/former | Status |
| ------------- | ---------------------------------------- | ------ |
| `ctor_checks_against_its_data_type` | `data_declarations_and_refusals_agree_with_kernel` | Ported |
| `ctor_fits_ascribed_instantiation` | Implicit constructor-argument elaboration; native constructors carry all arguments explicitly | Deferred |
| `ctor_nominal_distinctness_is_rejected` | `data_declarations_and_refusals_agree_with_kernel` | Ported |
| `data_case_checks_and_agrees` | `dependent_data_parameters_and_case_motives` | Ported |
| `data_case_empty_absurd_agrees` | `empty_data_elimination_preserves_the_ambient_scope` | Ported |
| `record_is_width_subtype_positive` | `record_width_depth_and_projection` | Ported |
| `record_is_width_subtype_negative` | `record_width_depth_and_projection` | Ported |
| `record_is_depth_subtype_positive` | Graded thunk former and its grade-subtyping rule | Deferred |
| `record_is_depth_subtype_negative` | Graded thunk former and its grade-subtyping rule | Deferred |
| `record_empty_is_the_record_top` | `record_width_depth_and_projection` | Ported |
| `record_unknown_field_breaks_transitivity` | Unknown-type former and gradual consistency reader | Deferred |
| `record_literal_infers_its_field_types` | `record_width_depth_and_projection` | Ported |
| `record_literal_checks_against_a_narrower_record` | `record_width_depth_and_projection` | Ported |
| `record_projection_reduces_and_stays_spine_local` | `core-nbe::eval::tests::native_records_and_cases_compute` | Ported |
| `a_record_module_projects_its_component_and_nothing_else` | `core-nbe::eval::tests::native_records_and_cases_compute` | Ported |
| `data_case_selects_arm_returns_three` | `core-nbe::eval::tests::native_records_and_cases_compute` | Ported |
| `data_case_on_non_ctor_is_stuck` | `core-nbe::eval::tests::native_records_and_cases_compute` | Ported |

The record depth witnesses in this port concern nested structural records; they do not stand in for the deferred graded-thunk witnesses. The evaluator's malformed non-constructor case is an explicit fault, not an invented constructor branch. Additional witnesses cover signature formation and invalidation, branch coverage, malformed tags and arities, admission renumbering, exact artifact decoding, and children beyond the former fixed three-child snapshot limit.
