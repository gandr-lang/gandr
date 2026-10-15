# gandr-core-term

The core call-by-push-value language: its syntax in a flat arena, the one unified typing context, the definition chain, and the per-scope definitional environment.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The core language between the surface syntax and the kernel, and the one context its typing rules read. Values and computations on the term side, value types and computation types on the type side, are nodes of an append-only `CoreArena` addressed by four typed `u32` ids. `Context` is the two-zone typing context `Γ; Σ`: flat, de Bruijn, id-addressed and name-free. `DefinitionChain` records each definition's body and unfolding height; `DefinitionalEnvironment` decides, scope by scope, whether a definition is manifest. `FailureClass` is the four-class vocabulary every refusal of the core pipeline is classified into. The crate holds syntax, contexts and native scalar operations; conversion lives in `gandr-core-nbe` and execution in `gandr-core-sequent`. It is `no_std` over `core` and `alloc`.

**Why.** An elaborator, a normalizer and a checker each go under binders, type occurrences and unfold definitions, and separate spellings of the context drift. One flat representation gives every rule one place to read a binder, and cloning it copies two flat vectors, so a conversion or a normalizer takes one by value. The core language needs formers the kernel does not represent, so its node enums are its own; its leaf vocabulary is the kernel's, so a core term erases to a kernel term by remapping ids.

**How.** A node holds its children as `Copy` ids minted only by constructors over children already minted, so teardown is a flat vector drop per family and the derived equality and hashing are shallow. De Bruijn indices make α-equivalence syntactic identity, so no freshness invariant is maintained. The context keeps one stack per zone, each with its own index space: `Γ` admits weakening and contraction, and `Σ` consumes a slot on its one occurrence. The definition chain names each body by a canonical subterm-table entry index, which is the same in every arena that decodes the artifact, and computes heights in one forward pass over admission order. The definitional environment is a forest of scopes whose parent always precedes the child, walked outward to the innermost override.

## Provided features

- `Value`, `Computation`, `ValueType` and `CompType`: core syntax, including dependent arrows, both universe towers, quotes and decodes, static operators, nominal Data applications and constructors, structural records, dependent cases, record projections, positional tuple projections, the fixpoint `Computation::Fixpoint` with its `FixpointEvidence`, the ascription `Computation::Ascribe` that synthesises the type it checks its body against, and native `PathUniverse`, `PathRefl`, `PathEquiv`, `PathProduct` and `Transport`.
- `Classifier`, `Sort` and `SortParameter`: a type's ground sort and level, and the sort a universe is written at.
- `shift_value_type`, `shift_comp_type`, `instantiate_comp_type`, `instantiate_value` and `strengthen_comp_type`, with `Binders`: the binder machines over types and codes.
- `CoreArena` with `ValueId`, `ComputationId`, `ValueTypeId` and `CompTypeId`: one constructor per former, a checked lookup per family, and `ArenaWatermark` with `CoreArena::truncate_to` and the per-family suffixes minted since a mark (`values_since`, `computations_since`, `value_types_since`, `comp_types_since`). Witness: `arena::tests::allocation_suffixes_keep_their_family`.
- Native `List` types, `ListNil` and `ListCons` values, and an annotated, pure `ListFold`; the cell branch binds the head followed by the folded result. These are the [kernel's List former](../kernel-core/src/check.rs), not a sum encoding or a nominal declaration.
- Closed effect rows on returners carry named interfaces with typed payloads and replies. `EffectRow::EMPTY` is the pure returner; unions and inclusions reject conflicting interfaces rather than replacing an operation type. The `effect::host` table supplies `Exec`, `Fs`, `Proc` and `Env` signatures, using native Lists and ordered products for record-shaped payloads.
- `TypeImporter` copies the graph reachable from type roots into another arena, preserving shared children across imports. The source and destination use the same binder context; `instantiate_value_type_under` closes ambient variables while preserving a chosen number of local binders. Witnesses: `import::tests::dependent_annotations_preserve_sharing_across_arenas`, `rewrite::tests::annotation_substitution_protects_local_binders`.
- `Context`: `open`, `close`, `occurrence`, `declared`, `linear_use` and `depth` over `Zone::Intuitionistic` and `Zone::Linear`, refusing with `ContextError`.
- `DefinitionChain`, `DefinitionEntry` and `DefinitionHeight`: `define`, `entry` and `entries`, refusing with `DefinitionError`.
- `DefinitionalEnvironment`, `ScopeId` and `Transparency`: `root`, `open_scope`, `state` and `transparency`.
- `FailureClass`: `UserAbsence`, `Unrepresentable`, `MalformedSource` and `EngineFault`, the classes a lowering refusal and a checking refusal are each classified into by their own crate's classifier.
- `Value::Hole`, `Value::Mark`, `Computation::Hole`, `Computation::Mark`, `ValueType::Unknown` and `CompType::Unknown`, with `hole::HoleId`, `hole::MarkIndex` and `hole::TermId`: the elaborator's hole surface. Witness: `rewrite::tests::a_fill_replaces_exactly_the_named_holes`.
- `hole::matched_thunk`, `matched_product` and `matched_sum` (answering `hole::Components`), `matched_static_pi`, `matched_list`, `matched_stack`, `matched_returner`, `matched_function` and `matched_with`, with `hole::Knowledge` and `hole::matching::Absent`: a type's former, or unknown components when the type is unknown. Witnesses: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`, `hole::tests::a_known_type_matches_only_its_own_former`, `hole::tests::the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not`.
- `fill_hole`, `wrap_marks` and `substitute_environment`: filling by name, marking by node, and closing a suspended body over its environment. Witnesses: `rewrite::tests::a_fill_replaces_exactly_the_named_holes`, `rewrite::tests::a_wrap_marks_exactly_the_named_nodes`, `rewrite::tests::an_environment_substitution_replaces_every_free_index`.
- `pattern::Pattern`, `pattern::Patterns`, `pattern::PatternId` and `pattern::BranchStatus`: patterns, pattern holes among them, and a branch's three answers. Witnesses: `pattern::tests::a_pattern_names_its_parts_in_order`, `pattern::tests::a_conjunction_refutes_first_and_doubts_second`.

## Expected features

- **One arena per run.** The caller keeps every id with the arena that minted it. The context, the chain and the environment store ids and never dereference them, and an arena lookup refuses an id it does not hold but cannot tell one minted by another arena.
- **Admission positions and subterm-table indices from the artifact.** `ConstantIndex` and `GlobalIndex` come from `gandr-kernel-term`; the chain checks their order and does not resolve them.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.

## Examples

Go under a binder, type its occurrence twice, and close it:

```rust
use gandr_core_term::Context;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

fn bind_and_close() {
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let mut context = Context::new();

    context.open(Zone::Intuitionistic, unit);
    let first = context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let again = context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    assert_eq!(first, again);
    assert_eq!(Ok(unit), context.close(Zone::Intuitionistic));
}
```

Define two definitions and seal the second outside an inner scope:

```rust
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionError;
use gandr_core_term::DefinitionHeight;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

fn seal() -> Result<(), DefinitionError> {
    let ground = ConstantIndex::from(0_usize);
    let derived = ConstantIndex::from(1_usize);
    let mut chain = DefinitionChain::new();
    let leaf = chain.define(ground, GlobalIndex::from(0_u32), Transparency::Manifest, &[])?;
    let above = chain.define(derived, GlobalIndex::from(1_u32), Transparency::Manifest, &[ground])?;
    assert_eq!(DefinitionHeight::from(1_u32), leaf);
    assert_eq!(DefinitionHeight::from(2_u32), above);

    let mut environment = DefinitionalEnvironment::new();
    let outside = environment.root();
    let inside = environment.open_scope(outside)?;
    environment.state(outside, derived, Transparency::Opaque)?;
    environment.state(inside, derived, Transparency::Manifest)?;
    assert_eq!(Transparency::Opaque, environment.transparency(outside, derived, Transparency::Manifest)?);
    assert_eq!(Transparency::Manifest, environment.transparency(inside, derived, Transparency::Manifest)?);
    Ok(())
}
```

Run the tests, then again with specifications enforced:

```sh
cargo nextest run -p gandr-core-term
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-core-term
```

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The kernel alphabet and the core grammar, nominal data and records, n-ary products and sums, native universe paths, static operators | [`syntax`](src/syntax.rs) |
| Holes, marks and the unknown type | [`hole`](src/hole.rs) |
| Patterns with holes | [`pattern`](src/pattern.rs) |
| The native prelude and its runtime assumptions | [`primitive`](src/primitive.rs) |
| Description decoding | [`description`](src/description.rs) |
| Universe families | [`classifier`](src/classifier.rs) |
| Quotes, decode-on-mint and arena ownership | [`arena`](src/arena.rs) |
| Binder machines | [`rewrite`](src/rewrite.rs) |
| Zones and the failure state | [`context`](src/context.rs) |
| Definition heights and per-scope transparency | [`definition`](src/definition.rs) |
| The failure vocabulary | [`failure`](src/failure.rs) |
| Effects, handlers and control | [`effect`](src/effect.rs), [`control`](src/control.rs) |
| Temporary access: hold, access, resume and abort | [`memory`](src/memory.rs) |
| References and specification attributes | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
