# gandr-core-term

The core call-by-push-value language: its syntax in a flat arena, the one unified typing context, the definition chain, and the per-scope definitional environment.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Kernel alphabet and core grammar](#kernel-alphabet-and-core-grammar)
- [Zone-qualified variables](#zone-qualified-variables)
- [Failure state](#failure-state)
- [Definition heights](#definition-heights)
- [Per-scope transparency](#per-scope-transparency)
- [Arena ownership](#arena-ownership)
- [One failure vocabulary](#one-failure-vocabulary)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The core language between the surface syntax and the kernel, and the one context its typing rules read. Values and computations on the term side, value types and computation types on the type side, are nodes of an append-only `CoreArena` addressed by four typed `u32` ids. `Context` is the two-zone typing context `Γ; Σ`: flat, de Bruijn, id-addressed and name-free. `DefinitionChain` records each definition's body and unfolding height; `DefinitionalEnvironment` decides, scope by scope, whether a definition is manifest. `FailureClass` is the four-class vocabulary every refusal of the core pipeline is classified into. The crate holds syntax and contexts; evaluation and readback live in `gandr-core-nbe`. It is `no_std` over `core` and `alloc`.

**Why.** An elaborator, a normalizer and a checker each go under binders, type occurrences and unfold definitions, and separate spellings of the context drift. One flat representation gives every rule one place to read a binder, and cloning it copies two flat vectors, so a conversion or a normalizer takes one by value. The core language needs formers the kernel does not represent, so its node enums are its own; its leaf vocabulary is the kernel's, so a core term erases to a kernel term by remapping ids.

**How.** A node holds its children as `Copy` ids minted only by constructors over existing children, so teardown is a flat vector drop per family and the derived equality and hashing are shallow. De Bruijn indices make α-equivalence syntactic identity, so no freshness invariant is maintained. The context keeps one stack per zone, each with its own index space: `Γ` admits weakening and contraction, and `Σ` consumes a slot on its one occurrence. The definition chain names each body by a canonical subterm-table entry index, which is the same in every arena that decodes the artifact, and computes heights in one forward pass over admission order. The definitional environment is a forest of scopes whose parent always precedes the child, walked outward to the innermost override.

## References

- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Semantics Structures in Computation 2, Kluwer Academic Publishers, 2003. `isbn:978-1-4020-1730-8`, `doi:10.1007/978-94-007-0954-6` — the polarity split that makes values and computations two vocabularies.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4's hash-consed subterm DAG, whose entry index the definition chain carries as an arena-independent name for a body.

## Provided features

- `Value`, `Computation`, `ValueType` and `CompType`: the core vocabulary, including the dependent function type `CompType::Pi` and the code-reading former `ValueType::Element`.
- `CoreArena` with `ValueId`, `ComputationId`, `ValueTypeId` and `CompTypeId`: one constructor per former, a checked lookup per family, and `ArenaWatermark` with `CoreArena::truncate_to`.
- `Context`: `open`, `close`, `occurrence`, `declared`, `linear_use` and `depth` over `Zone::Intuitionistic` and `Zone::Linear`, refusing with `ContextError`.
- `DefinitionChain`, `DefinitionEntry` and `DefinitionHeight`: `define`, `entry` and `entries`, refusing with `DefinitionError`.
- `DefinitionalEnvironment`, `ScopeId` and `Transparency`: `root`, `open_scope`, `state` and `transparency`.
- `FailureClass`: `UserAbsence`, `Unrepresentable`, `MalformedSource` and `EngineFault`, the classes a lowering refusal and a checking refusal are each classified into by their own crate's classifier.

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

## Kernel alphabet and core grammar

Levels, base types, literals, sum sides, de Bruijn indices, admission positions and subterm-table entry indices come from `gandr-kernel-strata` and `gandr-kernel-term`. The two languages therefore agree on what a literal or a level is, and erasing a core term to a kernel term remaps ids without translating payloads; the erasure itself is not in this crate. The node enums, the arena and the context are this crate's own, so an elaboration-only former enters the core grammar without widening the closed vocabulary the kernel represents.

## Zone-qualified variables

`Value::Variable` carries a `Zone` beside its index, because each zone counts binders in its own index space and an index alone names no binder. `Γ` admits weakening and contraction: an occurrence spends nothing. `Σ` is linear: an occurrence consumes its slot, a second occurrence is refused with `ContextError::LinearSlotConsumed`, and closing a scope whose slot is unspent is refused with `ContextError::LinearSlotUnconsumed`. The linear zone is the type-level form of "a control capture cannot be naively duplicated". No former in the vocabulary binds into `Σ`; a context opened with `Zone::Linear` reaches it directly, and the tests exercise both refusals there.

## Failure state

A failing context operation leaves the context at the failure point: a refused occurrence spends nothing, and a refused close leaves the binder in place. That state is the specification, and the tests assert it after every refusal. The context has one implementation, iterative, so no second face can unwind it differently.

## Definition heights

A definition's height is one above the tallest definition its body mentions; a definition that mentions none has height one. Zero means not unfoldable, and nothing in the chain has it: an axiom or a sealed atom has no body and is not in the chain. `DefinitionChain::define` refuses an entry out of admission order and a mention at or above its own position, so every mention's height is recorded before the mentioning entry and the height is one forward pass rather than a fixed point. A height is a scheduling prior: it weights which side of a conversion to unfold and never decides which unfoldings are attempted.

## Per-scope transparency

Transparent ascription makes the same atom manifest inside a sealed module and opaque outside it, so transparency is a property of a scope rather than of a definition. `DefinitionalEnvironment` is a flat forest of scopes; `transparency` walks outward from a scope and answers the innermost override, or the declaration's own stance when no scope states one. The empty environment, one root scope with no override, answers like a single global table.

## Arena ownership

An id is minted only by a `CoreArena` constructor over already-allocated children, so a child id always resolves and, within its family, is strictly less than its parent's. The four families index independently; acyclicity across them rests on minting order, since a constructor cannot name a node that does not exist yet. Lookups return `Option`, because a `u32` id can name no node. `CoreArena::watermark` snapshots the four family lengths and `CoreArena::truncate_to` restores them, so a pass's intermediates allocate past a mark and drop in one step. The arena offers constructors and lookups only; each walk over its edges belongs to the consumer that needs it.

## One failure vocabulary

`FailureClass` lives here because this is the lowest crate both the lowering and the checker depend on: each classifies its own refusals with its own `const`, wildcard-free match, and a report groups both under one enum without either crate naming the other. The type carries no behaviour beyond its name; which refusal falls in which class is decided by the crate that owns the refusal. The alternative was a copy of the enum in each producer, kept equal by convention, which is two vocabularies a report would have to reconcile. Reversal: a producer whose failures need a class the others do not have, at which point that class is argued here rather than added in the producer.

## Specification attributes

Each item's `# Specification` prose is the statement of record. Where a clause is a cheap predicate over one call, a `#[spec(...)]` attribute states it verbatim, and a postcondition is stated by an independent reading — a linear scan against the chain's binary search, an inward count against the shared offset arithmetic — rather than the body's own expression read back. `Context::open` and `Context::occurrence` stay prose: each postcondition relates every slot of the context before and after the call, which only an allocating snapshot could observe.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
