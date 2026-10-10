# gandr-core-term

The core call-by-push-value language: its syntax in a flat arena, the one unified typing context, the definition chain, and the per-scope definitional environment.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Kernel alphabet and core grammar](#kernel-alphabet-and-core-grammar)
- [Universe families](#universe-families)
- [Quotes and decode-on-mint](#quotes-and-decode-on-mint)
- [Static operators](#static-operators)
- [Binder machines](#binder-machines)
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
- Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV's two levelled universe towers, and no kind layer above them.
- Josselin Poiret, Gaëtan Gilbert, Kenji Maillard, Pierre-Marie Pédrot, Matthieu Sozeau, Nicolas Tabareau and Éric Tanter. "All Your Base Are Belong to Us: Sort Polymorphism for Proof Assistants." _Proceedings of the ACM on Programming Languages_ 9 (POPL), 2025. `doi:10.1145/3704912` — the sort separated from the level and quantified over, which `Sort::Parameter` leaves room for.

## Provided features

- `Value`, `Computation`, `ValueType` and `CompType`: core syntax, including dependent arrows, both universe towers, quotes and decodes, static operators, and native `PathUniverse`, `PathRefl`, `PathEquiv`, `PathProduct` and `Transport`.
- `Classifier`, `Sort` and `SortParameter`: a type's ground sort and level, and the sort a universe is written at.
- `shift_value_type`, `shift_comp_type`, `instantiate_comp_type`, `instantiate_value` and `strengthen_comp_type`, with `Binders`: the binder machines over types and codes.
- `CoreArena` with `ValueId`, `ComputationId`, `ValueTypeId` and `CompTypeId`: one constructor per former, a checked lookup per family, and `ArenaWatermark` with `CoreArena::truncate_to`.
- `Context`: `open`, `close`, `occurrence`, `declared`, `linear_use` and `depth` over `Zone::Intuitionistic` and `Zone::Linear`, refusing with `ContextError`.
- `DefinitionChain`, `DefinitionEntry` and `DefinitionHeight`: `define`, `entry` and `entries`, refusing with `DefinitionError`.
- `DefinitionalEnvironment`, `ScopeId` and `Transparency`: `root`, `open_scope`, `state` and `transparency`.
- `FailureClass`: `UserAbsence`, `Unrepresentable`, `MalformedSource` and `EngineFault`, the classes a lowering refusal and a checking refusal are each classified into by their own crate's classifier.

Native path certificates share the kernel's portable `PathEvidence` vocabulary. Arena identity and content hashing retain evidence; `equal_certificate_syntax` compares raw certificate syntax while erasing evidence only. It does not turn computationally equivalent maps into identical certificates. Binder rewrites traverse classifier codes and translator bodies normally. **Choice:** mirror native syntax rather than maintain a second path arena. **Reversal:** extending the closed code fragment requires corresponding kernel admission and replay rules, not a syntax-only frontend permission.

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

## Universe families

A type is classified by a `Classifier`: a ground sort, `GroundSort::Value` (`+`) or `GroundSort::Computation` (`-`), and a level from `gandr-kernel-strata`. There are two towers, `ValueType::Universe { sort, level }` for each sort, and both are value types: a universe classifies codes, and a code is a value whichever sort the type it names has, so `Type[+, l]` and `Type[-, l]` each live in `Type[+, l + 1]`. The ground sort is the kernel's, from `gandr-kernel-term`, so the two languages read one alphabet; the core's `Sort` adds `Sort::Parameter`, a sort variable, so that abstracting over a sort raises the exact variant the term would have needed. No producer writes a sort parameter, and the checker refuses one: it is the seat sort polymorphism arrives through, monomorphized away before the kernel.

Alternatives: one universe tower with a polarity bit on each code, which makes every code-reading rule ask which side it is on and hides the sort from the level; and a kind layer above the two towers, which ∂CBPV shows is not needed. Reversal: a computation type that classifies codes, which would put a universe in the computation family.

## Quotes and decode-on-mint

`Value::Quote` names a value type as a code and `Value::QuoteComputation` a computation type; `ValueType::Element` and `CompType::Element` read a code back as the type it names. `CoreArena::value_type_element` and `CoreArena::comp_type_element` decode on mint: given a quote of the matching family as the code, they return the quoted type itself rather than minting a decode of it, so `El(⌜A⌝)` and `A` are one id and no conversion ever meets the redex. The level a decode carries is the code's universe level, and a decode of a quote ignores it: the quoted type has its own.

Alternatives: a decode node kept over a quote and the β-rule left to conversion, which every comparison of a type then pays and the kernel would have to fire too. Reversal: a decode whose quote is only known after substitution still meets the rule, so a machine that substitutes a quote for a code variable re-mints the decode through the same constructor (`instantiate_comp_type` does).

## Static operators

A type operator such as `\A. A * A` is a code-level function: it takes codes and returns a code, and it is gone before runtime. The core spells it with three value-family formers. `ValueType::StaticPi { domain, codomain }` classifies operators; `Value::StaticLambda` abstracts over one intuitionistic binder; `Value::StaticApplication` applies an operator to a code. All three are values because codes are values (§ Universe families): an operator is a code that awaits codes, so it lives where codes live, and an application is a code too. It decodes through `ValueType::Element` or `CompType::Element` like any other code.

The static Pi is non-dependent: its codomain stands in the ambient context, as `CompType::Arrow`'s does, not under a binder. Its domain and codomain are themselves static classifiers: universes, or static Pis over them. That is the simply kinded discipline of System Fω, enough for a family such as `Type -> Type[-]` and for a relative monad's carrier. Dependency at the type level would make classifiers mention codes, and with them the kernel's conversion would have to compare open codes.

A static application whose head is a static lambda is a redex, and the arena represents it. Arena constructors do not reduce it. Static beta belongs to the normalizer in `gandr-core-nbe`, which reads back static normal forms, and `instantiate_value` is the one substitution step a certificate replays. Keeping the redex representable means the elaborator can write a family's use as it stands in the source, and the checker can name each unfolding it performs.

Alternatives:

- a separate static-term language with its own arena family, which duplicates every walk, every binder machine and every content codec;
- type operators as computation-family functions over thunked codes, which puts code-level reduction under effects;
- reduce on mint, as decode does, which would hide the redex the certificate names and would need substitution inside the arena.

Reversal: a family whose classifier must mention a code, at which point the static Pi gains a binder and the kernel's conversion gains open codes.

## Binder machines

A dependent arrow's codomain stands under one binder, so the checker shifts and instantiates types. `shift_value_type` and `shift_comp_type` raise the free indices of the intuitionistic zone at or past a cutoff; `instantiate_comp_type` substitutes a value for the innermost index and lowers the rest; `strengthen_comp_type` lowers a type out of one binder or refuses with `strengthening::Absent::MentionsBinder` when the type mentions it. Each runs on a heap task stack, never recursing, and memoizes per node and binder depth, so a shared subterm is rewritten once per depth it is reached at. A replacement carried under a binder is shifted once per depth and recorded, so substitution avoids capture without renaming anything. The linear zone is left alone: no former in the vocabulary binds into it.

Alternatives: recursive rewrites, which the workspace's recursion lint forbids and which a deep type would overflow; and explicit substitutions held lazily in the arena, which every reader would then have to push through. Reversal: a measured family whose cost is dominated by the eager rewrite, which would hold substitutions as closures the way the normalizer already does.

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
