# gandr-runtime-compile-host

Feature-gated preparation of positive-core program images for a compilation host.

## Contents

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Feature boundary](#feature-boundary)
- [Image and C boundary](#image-and-c-boundary)
- [Typed admission](#typed-admission)
- [Evidence and deferred rows](#evidence-and-deferred-rows)
- [Mutation backlog](#mutation-backlog)
- [License](#license)

## Synopsis

**What.** This crate lowers the L machine's positive core into a bounded, dependency-ordered image, encodes that image, checks typed admission, represents the versioned C boundary and renders terminal values in the host's comparison grammar.

**Why.** The runtime tier needs an explicit boundary between core computations and effectful compilation. Preparing an image must not load a host, acquire a compiler toolchain or claim that a program has run.

**How.** An explicit work stack borrows core-arena nodes and emits children before parents, ending in one terminal cut. De Bruijn indices retain their binder distances. The typed entry runs the core checker first; the independent machine entry only lowers. Wire goldens and L-machine readback exercise the public surface without a foreign host.

## References

- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Springer, 2003. ISBN 978-1-4020-1730-8 — the value/computation split.
- Pierre-Louis Curien and Hugo Herbelin. “The Duality of Computation.” _ICFP 2000_, pages 233–243. DOI [10.1145/351240.351262](https://doi.org/10.1145/351240.351262) — cuts and sequencing consumers.
- N. G. de Bruijn. “Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation, with application to the Church-Rosser theorem.” _Indagationes Mathematicae (Proceedings)_ 75(5), 1972, pages 381–392. DOI [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258(72)90034-0) — binder distances.

## Provided features

| Surface | Provision |
| ------- | --------- |
| `lower_computation` | Closed integers, unit, pairs, injections, return, bind and case; explicit excluded-form, scope, address and size refusals |
| `Image` | Bounded records, backward operands, signed 64-bit literals and little-endian version-one encoding |
| `check_and_lower`, `is_typed` | Core checking at a formed expected computation type before image preparation; typed refusal payloads |
| `boundary` | C outcome layout, ABI version, status interpretation, owned answer and refusal types |
| `render::canonical` | Iterative rendering as `(int N)`, `(unit)`, `(pair V V)`, `(inl V)` or `(inr V)` |

## Expected features

Consumers enable `compile-host` explicitly and supply arena ids from the accompanying core arena. Typed requests supply a `CheckingContext` and its formed expected type. Raw C records remain borrowed foreign data: their text pointer conveys neither Rust ownership nor permission to dereference it.

## Examples

Exercise the public lowering, encoder, checker and L-machine rendering witnesses:

```sh
cargo test -p gandr-runtime-compile-host
RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-runtime-compile-host
cargo tree -p gandr-runtime-compile-host --no-default-features --edges normal
```

`tests::rendering::supported_programs_render_the_l_machines_pinned_answers` focuses five closed programs through `gandr-core-sequent`, runs its public machine, reads the terminal back and compares independent grammar goldens. `tests::typed::the_typed_verdict_reports_what_the_checker_would_say` exercises typed admission and refusal from outside the library.

## Feature boundary

The ordinary crate has no default features or normal dependencies. Its own development dependency enables `compile-host` only for tests and all-target policy checks, so the workspace witness inventory cannot silently omit the optional implementation. Rustdoc explicitly covers all features. The driver has no dependency on this crate and exposes no compiled execution verb.

The implementation has no build script, foreign declarations, dynamic loader, C++ build step or host execution fallback. It uses existing workspace dependencies; a Rust host over generated MLIR bindings owns execution and message release.

The choice is a feature-gated Rust preparation library. Linking a foreign host would put platform/toolchain effects in the build graph; an always-enabled preparation library would make the opt-in boundary ineffective. Revisit when the Rust compile host supplies an executable consumer and its toolchain lane.

## Image and C boundary

Image version one starts with a u8 version and a little-endian u16 node count. Each record writes kind (u8), constructor (u8), binder (u32), literal (i64), operand count (u8), then ordered operand addresses (u32). The node ceiling is 4096. Append refuses oversized operand lists and forward references before mutation; encoding never silently truncates a caller's record.

| Vocabulary | Assigned values |
| ---------- | --------------- |
| Node kinds | Lit 0, Var 1, Ctor 2, Dup 3, Drop 4, Bind 5, Case 6, Cut 7 |
| Constructor tags | Unit 0, Pair 1, Inl 2, Inr 3 |
| ABI version | 1 |
| Statuses | success 0; decoder 1; verifier 2; lowering 3; LLVM conversion 4; execution 5; renderer 6; limit 7; fixture 8; bad call 100 |

Unknown statuses retain their numeric code. `RawOutcome` uses C layout in this order: i32 status, i64 duplications, i64 discards, u64 allocated words, C character pointer. Its alignment follows the target C ABI. Tests assert widths and offsets directly rather than inspecting another implementation's source text.

Dup and Drop remain representable image operations with separate static counts. A case makes those counts upper bounds because only one arm executes. Core lowering cannot emit these operations until core grade formers exist. The flat arena and explicit traversal avoid owning recursive terms and cloning the input arena; they preserve the fixed wire instead of introducing a general serialization framework.

## Typed admission

The checker owns acceptance. The caller supplies a formed expected type; this boundary neither synthesizes a missing type nor invents an unknown type. A typed text value therefore reaches `NotLowered(OutsideSlice(String))`, while an ill-typed case reaches `NotChecked` first.

Return and injection introductions are check-only in the current core. A bind's bound computation and a case's scrutinee must synthesize there, so direct return-bound and injection-scrutinee machine examples are not automatically typed examples. This API preserves those checker refusals; it does not weaken the judgement to admit machine programs. Core annotation/synthesis support and grade formers govern the complete typed-versus-machine floor.

## Evidence and deferred rows

The 40 named floor obligations comprise 19 ported obligations and 21 deferred obligations. Wire and ABI assertions are semantic goldens, not source-spelling checks. The wrapper-only obligation is covered by signed payload boundaries and separately counted operations; the bridge-message obligation is covered by typed stage and payload assertions rather than diagnostic wording.

The five-program witnesses state their restricted domain explicitly. They do not claim the eight-program floor, whose duplication, discard and accounted-work programs require grade formers. Every deferred host row waits for **the Rust compile host**; its exact name is the execution boundary's drop-in obligation.

| Deferred obligation | Required reader or former |
| ------------------- | ------------------------- |
| `lowering::every_named_program_lowers_to_an_arena_ending_in_its_cut` | core Dup/Drop formers and grade typing |
| `lowering::every_operand_addresses_a_strictly_earlier_node` | core Dup/Drop formers and grade typing |
| `lowering::the_typed_gate_admits_the_typed_programs_and_refuses_the_grade_ones` | core Dup/Drop formers and grade typing |
| `lowering::every_excluded_core_form_is_refused_by_name` | the core List former |
| `rendering::every_named_program_renders_its_own_answer` | core Dup/Drop formers |
| `contract::the_heap_layout_is_what_the_bridge_assumes` | the Rust compile host |
| `contract::the_cell_tag_numbering_is_unchanged` | the Rust compile host |
| `contract::the_verifier_still_opens_the_pipeline` | the Rust compile host |
| `contract::the_grade_operations_still_declare_their_effects` | the Rust compile host |
| `contract::the_agreement_fixture_names_this_crates_programs` | the Rust compile host |
| `host::every_host_failure_renders_its_own_message` | the Rust compile host |
| `host::the_boundaries_values_round_trip_through_their_wrappers` | the Rust compile host |
| `host::a_null_boundary_message_reads_as_empty` | the Rust compile host |
| `bridge::the_bridge_agrees_with_the_l_machine_on_every_named_program` | the Rust compile host |
| `bridge::the_bridge_agrees_with_the_image_on_accounted_work` | the Rust compile host |
| `bridge::the_two_host_paths_agree_through_the_bridge` | the Rust compile host |
| `bridge::the_bridge_sees_the_compiled_bounds_check` | the Rust compile host |
| `bridge::a_computation_outside_the_slice_is_refused_before_the_boundary` | the Rust compile host |
| `bridge::a_boundary_symbol_that_drifts_fails_at_link_time` | the Rust compile host |
| `compile_host_agreement::the_fixture_states_what_the_l_machine_answers` | the Rust compile host and core Dup/Drop formers |
| `compile_host_agreement::every_sampled_transition_reaches_its_own_answer` | the Rust compile host and core Dup/Drop formers |

## Mutation backlog

The following scope waits for a standalone campaign, not a landing gate. No mutation adequacy score is claimed; a campaign must refuse zero viable mutants or an unexercised baseline.

| Package and commit range | Scope | Hypothesis items |
| ------------------------ | ----- | ---------------- |
| `gandr-runtime-compile-host`, `84b94d316a1c961fc89072a79b855a7d87b0c6aa..HEAD` restricted to this crate | `src/{image,lower,typed,boundary,render}.rs` | The adjacent adequacy hypotheses: tags and arities, byte order, signed endpoints, binder and field order, checker-first refusal, status decoding, ABI layout and canonical grammar |

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
