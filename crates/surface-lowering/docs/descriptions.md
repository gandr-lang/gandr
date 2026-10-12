# Descriptions, cells and circuit wiring

The description route of `gandr-surface-lowering`: `data`, `codata` and `sign` declarations read into checked descriptions, the families the native data reading does not own decoded into core signatures, operation and rule members elaborated into cells, and literal circuit wiring handed to the circuit-algebra matcher. The crate's [README](../README.md) states the rest of the crate, and [docs/native.md](native.md#native-data-and-the-match) the native data reading this route stands beside.

<!-- toc -->

- [Declarations read into descriptions](#declarations-read-into-descriptions)
- [One producer for a data form](#one-producer-for-a-data-form)
- [Signature blocks](#signature-blocks)
- [Cells and circuit wiring](#cells-and-circuit-wiring)
- [Floor](#floor)

<!-- tocstop -->

## Declarations read into descriptions

`description::elaborate_descriptions` reads top-level `data`, `codata` and `sign` declarations into checked descriptions. Typed family parameters and classifiers are retained separately from the description code. Constructor results must name the declared family with the same parameter variables, in order; declared value-index positions stay expressions rather than being read as field types. A malformed member earns its own diagnostic without removing readable siblings. The report retains structured well-formedness diagnostics and their available source spans.

## One producer for a data form

A `data` form has one producer of its signature: the [native reading](native.md#native-data-and-the-match), which lowers it to `DeclarationOutcome::Data`, enters its constructors and compiles the matches over it. The description route reads the same form beside it and owns what the native reading passes over. Its `oper` and `rule` members become description and cell entries, and a refusal among them is a held declaration at the member's own span under the family's name. It neither replaces the family's native signature nor consumes the declarations after the block. Every other described family with a classifier — `codata` today — is admitted at its own position and decoded from its description by `decode_signature`, under all family parameters, with later applications keeping the family's admission identity. The decoder's refusal, `CodataNu` for codata, refuses that family alone, at its span. An attribute block written before an admitted family decorates it, as one before a `data` family does, so a corpus fixture states the refusal it expects (`description::tests::an_attribute_block_decorates_the_codata_declaration_after_it`).

**Choice.** One producer per declaration form. The recorded design had the description decoder produce `data` signatures as well. Two producers for one form let a native signature and a decoded one disagree about the same family, and only the native reading enters constructors and compiles matches. The alternatives were the decoder as the sole producer, which must first reproduce native constructor entry and match compilation, and both producers behind an agreement check, which reads every data family twice. A nominal native family is preserved rather than replaced by a structural coproduct or an opaque value declaration, and descriptive polarity stays separate from core representability: a readable `codata` description is not silently reinterpreted as a positive record. **Reversal.** A decoder that agrees with the native reading on every data form, constructors and matches included, can replace it as the producer. Further core readings arrive only with their formation and checking rules.

Witnesses: `description::tests::native_data_keeps_telescope_and_nominal_heads`, `description::tests::member_refusals_keep_their_spans_and_other_declarations`, `description::tests::codata_is_refused_by_the_decoder_and_data_beside_it_is_native`, `lower::native::tests::operation_and_rule_members_are_left_to_the_description_route`, and the description reader's declaration and refusal witnesses in `description::tests`.

## Signature blocks

A `sign` block is a description judgment, not an ordinary native value family: it has no family classifier and creates no placeholder core value. It retains declared sorts and their index telescopes, operation boundaries and circuit rules. A rewrite port is instantiated at its written wiring; the body derives both sphere endpoints. A cycle or a derivation ceiling refuses that derivation rather than fabricating a boundary. A feed back-edge is a located wheel-boundary refusal, not an ordinary frame. Witnesses: `description::sign::tests::a_ruled_sign_block_lowers_its_members_into_a_description`, `description::sign::tests::a_feed_statement_declines_naming_the_wheel_obligation`.

## Cells and circuit wiring

`desc_cells::elaborate_desc_cells` turns each description into one declaration-local cell store, retaining operation frames, circuit composites and typed refusals. Ordinary `lower_module` collection executes this route and exposes the result through `LoweredModule::cells`; cell refusals become held declarations at their own operation or rule spans. A many-output operation elaborates to one frame with a return continuation per output port, and its rules elaborate over that frame; a rule returning a different number of results is refused at its own span. A `data` operation whose rules compile runs as a declaration of the module, returning its results as one tuple (`operation`). Identical faces share one cell identity. Witnesses: `desc_cells::tests::ordinary_lowering_executes_the_cell_gate_and_preserves_later_values`, `desc_cells::tests::a_face_declared_twice_is_one_cell`, `desc_cells::tests::a_single_redex_block_reaches_the_cell_layer_behind_the_gate`, `desc_cells::tests::a_many_out_operation_rule_becomes_a_cell_with_a_continuation_per_output`, `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`.

`circuit::embed` reads literal port wiring into the circuit-algebra matcher. Equal spelling in different generator roles remains distinct, and an exhausted search budget is a refusal rather than an empty match set. This uses the shared diagram checker and embedding certificates instead of an independent adjacency matcher. Witnesses: `circuit::embed::tests::one_spelling_in_two_roles_is_two_boxes`, `circuit::embed::tests::an_exhausted_budget_declines_rather_than_reporting_no_match`.

## Floor

The prior engine's description suites, ported by name where the route reads what they test:

| Suite | Rows | Ported | Not yet ported |
| ----- | ---: | -----: | -------------: |
| `circuit_desc` | 21 | 20 | 1 |
| `circuit_embed` | 15 | 7 | 8 |
| `circuit_ports` | 13 | 0 | 13 |
| `circuit` | 8 | 0 | 8 |
| `desc_elab` | 19 | 19 | 0 |
| `desc_cells` | 7 | 7 | 0 |
| `sign_members` | 5 | 4 | 1 |
| `decode` | 9 | 9 | 0 |

`a_repeated_argument_name_reaches_the_linearity_refusal` ports its cell half: the boundary that copies a port is refused as a non-linear cell pattern. The rows not yet ported wait for readers this route does not have:

- **The port name-set fold (14):** every `circuit_ports` row, `the_name_set_fold_reaches_the_description_route_as_a_production_check`, and the consumed-twice half of the linearity row. The fold gives each port name of a circuit body one verdict — bound, shared, consumed twice, disagreeing in sort, closing a feed wheel — before derivation. Here the derivation refuses a cycle and the cell layer a copied port, and no per-name verdict exists.
- **The whole-source arrow pass (8):** every `circuit` row. The route confirms each node's arrow against its head as it reads the member (`description::sign::tests::node_arrow_resolution_distinguishes_declared_and_unknown_heads`); a pass over a whole source with its own refusals is not ported.
- **Overlaps into completion (8):** `the_description_route_records_where_one_rule_occurs_in_another`, `a_constructor_line_is_a_value_generator_and_every_refusal_renders`, `the_multi_root_and_reconvergent_case_stays_matcher_only`, `w1_two_embeddings_supply_two_critical_pairs`, `w2_embedding_supplies_a_non_unifying_sequent_pair`, `w3_deduplicated_declarations_keep_replay_attribution`, `w4_distinct_wire_renderings_keep_origin_seams` and `the_description_route_preserves_a_bounded_completion_decline`. The matcher is reached through `circuit::embed`; recording one rule's occurrences in another and feeding the critical pairs to completion is not. Identical and alpha-variant rule spellings collapsing to one overlap family lands with it.
- **An unterminated last member (1):** `a_single_member_needs_no_terminator`. The block's closing tile reaches the last member's run when that member has no `;`, so the member is refused as malformed rather than read. This is an open defect of the member split, not a missing former.
