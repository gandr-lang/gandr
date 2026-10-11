# gandr-core-term

The core call-by-push-value language: its syntax in a flat arena, the one unified typing context, the definition chain, and the per-scope definitional environment.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Kernel alphabet and core grammar](#kernel-alphabet-and-core-grammar)
- [Typed holes, marks and the unknown type](#typed-holes-marks-and-the-unknown-type)
- [Patterns with holes](#patterns-with-holes)
- [Native prelude](#native-prelude)
- [Native runtime assumptions](#native-runtime-assumptions)
- [Nominal data and structural records](#nominal-data-and-structural-records)
- [Native universe paths](#native-universe-paths)
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

**What.** The core language between the surface syntax and the kernel, and the one context its typing rules read. Values and computations on the term side, value types and computation types on the type side, are nodes of an append-only `CoreArena` addressed by four typed `u32` ids. `Context` is the two-zone typing context `Γ; Σ`: flat, de Bruijn, id-addressed and name-free. `DefinitionChain` records each definition's body and unfolding height; `DefinitionalEnvironment` decides, scope by scope, whether a definition is manifest. `FailureClass` is the four-class vocabulary every refusal of the core pipeline is classified into. The crate holds syntax, contexts and native scalar operations; conversion lives in `gandr-core-nbe` and execution in `gandr-core-sequent`. It is `no_std` over `core` and `alloc`.

**Why.** An elaborator, a normalizer and a checker each go under binders, type occurrences and unfold definitions, and separate spellings of the context drift. One flat representation gives every rule one place to read a binder, and cloning it copies two flat vectors, so a conversion or a normalizer takes one by value. The core language needs formers the kernel does not represent, so its node enums are its own; its leaf vocabulary is the kernel's, so a core term erases to a kernel term by remapping ids.

**How.** A node holds its children as `Copy` ids minted only by constructors over existing children, so teardown is a flat vector drop per family and the derived equality and hashing are shallow. De Bruijn indices make α-equivalence syntactic identity, so no freshness invariant is maintained. The context keeps one stack per zone, each with its own index space: `Γ` admits weakening and contraction, and `Σ` consumes a slot on its one occurrence. The definition chain names each body by a canonical subterm-table entry index, which is the same in every arena that decodes the artifact, and computes heights in one forward pass over admission order. The definitional environment is a forest of scopes whose parent always precedes the child, walked outward to the innermost override.

## References

- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Semantics Structures in Computation 2, Kluwer Academic Publishers, 2003. `isbn:978-1-4020-1730-8`, `doi:10.1007/978-94-007-0954-6` — the polarity split that makes values and computations two vocabularies.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4's hash-consed subterm DAG, whose entry index the definition chain carries as an arena-independent name for a body.
- Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV's two levelled universe towers, and no kind layer above them.
- Josselin Poiret, Gaëtan Gilbert, Kenji Maillard, Pierre-Marie Pédrot, Matthieu Sozeau, Nicolas Tabareau and Éric Tanter. "All Your Base Are Belong to Us: Sort Polymorphism for Proof Assistants." _Proceedings of the ACM on Programming Languages_ 9 (POPL), 2025. `doi:10.1145/3704912` — the sort separated from the level and quantified over, which `Sort::Parameter` leaves room for.
- Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A. Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus." _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — the hole and mark formers, the unknown type and the matched-type operations.
- Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_ 3 (POPL), 2019. <https://doi.org/10.1145/3290327> — filling as substitution of the hole by its fill, the syntactic half `fill_hole` provides.
- Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048> — the pattern hole and the three answers a branch can get.
- Eric Zhao et al. "Total Type Error Localization and Recovery with Holes." _Proceedings of the ACM on Programming Languages_ 8 (POPL), 2024. <https://doi.org/10.1145/3632910> — the mark former as the place an error stands, and `wrap_marks` as the elaboration's last step.
- Luc Maranget. "Warnings for pattern matching." _Journal of Functional Programming_ 17(3) (2007). <https://doi.org/10.1017/S0956796807006223> — the coverage questions the pattern table is read for, answered in `gandr-core-checker`.

## Provided features

- `Value`, `Computation`, `ValueType` and `CompType`: core syntax, including dependent arrows, both universe towers, quotes and decodes, static operators, nominal Data applications and constructors, structural records, dependent cases, record projections, the fixpoint `Computation::Fixpoint` with its `FixpointEvidence`, and native `PathUniverse`, `PathRefl`, `PathEquiv`, `PathProduct` and `Transport`.
- `Classifier`, `Sort` and `SortParameter`: a type's ground sort and level, and the sort a universe is written at.
- `shift_value_type`, `shift_comp_type`, `instantiate_comp_type`, `instantiate_value` and `strengthen_comp_type`, with `Binders`: the binder machines over types and codes.
- `CoreArena` with `ValueId`, `ComputationId`, `ValueTypeId` and `CompTypeId`: one constructor per former, a checked lookup per family, and `ArenaWatermark` with `CoreArena::truncate_to`.
- `Context`: `open`, `close`, `occurrence`, `declared`, `linear_use` and `depth` over `Zone::Intuitionistic` and `Zone::Linear`, refusing with `ContextError`.
- `DefinitionChain`, `DefinitionEntry` and `DefinitionHeight`: `define`, `entry` and `entries`, refusing with `DefinitionError`.
- `DefinitionalEnvironment`, `ScopeId` and `Transparency`: `root`, `open_scope`, `state` and `transparency`.
- `FailureClass`: `UserAbsence`, `Unrepresentable`, `MalformedSource` and `EngineFault`, the classes a lowering refusal and a checking refusal are each classified into by their own crate's classifier.
- `Value::Hole`, `Value::Mark`, `Computation::Hole`, `Computation::Mark`, `ValueType::Unknown` and `CompType::Unknown`, with `hole::HoleId`, `hole::MarkIndex` and `hole::TermId`: the elaborator's hole surface. Witness: `rewrite::tests::a_fill_replaces_exactly_the_named_holes`.
- `hole::matched_thunk`, `matched_product`, `matched_sum`, `matched_static_pi`, `matched_returner` and `matched_function`, with `hole::Knowledge` and `hole::matching::Absent`: a type's former, or unknown components when the type is unknown. Witnesses: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`, `hole::tests::a_known_type_matches_only_its_own_former`, `hole::tests::the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not`.
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

## Kernel alphabet and core grammar

Levels, base types, literals, sum sides, de Bruijn indices, admission positions and subterm-table entry indices come from `gandr-kernel-strata` and `gandr-kernel-term`. The two languages therefore agree on what a literal or a level is, and erasing a core term to a kernel term remaps ids without translating payloads; the erasure itself is not in this crate. The node enums, the arena and the context are this crate's own, so an elaboration-only former enters the core grammar without widening the closed vocabulary the kernel represents.

## Typed holes, marks and the unknown type

`Value::Hole` and `Computation::Hole` are holes the author left in a body, named by a `HoleId`; `Value::Mark` and `Computation::Mark` wrap a term an elaboration found ill-typed, naming the entry of its mark table by a `MarkIndex`. `ValueType::Unknown` and `CompType::Unknown` are the types a hole and a mark have when nothing hands them one (Hazelnut, POPL 2017). All six are elaboration-only: the kernel's closed vocabulary has none of them, so the bridge that erases a core term refuses a hole and the unknown type and erases a mark to its body.

A rule that demands a former of a type reads it through the matched-type operations in `hole`: a known type answers its former's components or that it has another former, and the unknown type answers its former with unknown components, so an introduction checks against the unknown type and an elimination of a term of the unknown type goes on. A decode of a hole or a mark is the unknown type too, read through `value_type_knowledge` and `comp_type_knowledge`, without minting a node. A matched dependent arrow reports whether its codomain stands under the argument's binder, so the checker shifts only what the scoping requires.

`fill_hole` replaces every hole of a name by its fill, written in the context the hole stands in, so a fill is a substitution of syntax rather than of a value under binders (Live Functional Programming with Typed Holes, POPL 2019); `wrap_marks` wraps each named node once, which is how a total elaboration returns its marked term (Zhao et al., POPL 2024). Both run on the binder machines' heap task stack and reuse every subterm they do not change. The alternative was a hole carrying its expected type, which ties the term to one elaboration; the type is the judgement's answer, and the hole is only its name.

## Patterns with holes

The core calculus eliminates by case, data case and projection, and has no match. `pattern::Patterns` is the vocabulary a match's arms are written in — wildcard, binder, unit, literal, pair, injection, constructor and the pattern hole — minted part before whole into a flat table, so every walk is a loop over ids. A pattern hole is neither a wildcard nor an absurd pattern: a fill may make it either, so a question about a match with one has an answer only when every filling gives the same one (Yuan et al., OOPSLA 2023). `BranchStatus` is that answer for one branch: satisfied, refuted, or possibly. Live matching in `gandr-core-nbe` and coverage (Maranget, JFP 2007) in `gandr-core-checker` read the same table. A core match former becomes worth its kernel translation once a consumer needs nested patterns to survive into the core term rather than being compiled away.

## Native prelude

`primitive::PRELUDE` is the single table of native names, operator spellings, ordered argument classifiers, result classifiers and evaluation instructions. Recognition seeds these rows; the checker reads their signatures; the sequent machine calls their evaluator. Native function values are closed, typed thunks of ordinary curried lambdas, so partial application uses the existing closure machine rather than a second calling convention.

| Family | Names | Types |
| ------ | ----- | ----- |
| Integer arithmetic | `add`, `sub`, `mul`, `int.div`, `int.mod`, `neg` | Integer operands and result |
| Integer comparison | `eq`, `ne`, `lt`, `le`, `gt`, `ge` | Integer operands, boolean result |
| Boolean logic | `and`, `or`, `bool.not` | Boolean operands and result |
| Integer combinators | `prim.id`, `prim.const` | Integer operands and result |

Booleans are `Unit + Unit`, with the left injection true. Division truncates toward zero; remainder has the dividend's sign. Division and remainder by zero return `PrimitiveError::DivisionByZero`, not a host panic. Arity and classifier errors stay distinct. Integer arithmetic preserves the literal vocabulary's unbounded magnitude, including values wider than a machine integer.

**Choice.** [num-bigint](https://github.com/rust-num/num-bigint), with defaults off, supplies exact arithmetic in `no_std + alloc`. The maintained pure-Rust implementation avoids hand-written arithmetic and a native build dependency. Fixed-width `bnum` cannot implement the literal contract; `rug` brings GMP; `malachite` brings a larger arithmetic surface and LGPL licensing. Revisit if measured arithmetic workloads justify a different backend without changing integer semantics. Native operands borrow decimal payloads until arithmetic requires conversion.

Native execution belongs to the sequent runtime. The pure normalizer reports `EvalFault::NativePrimitive` rather than inventing a native reduction rule. Persistence records the table name and ordered operands, never a function pointer or process-local address.

Witnesses: `primitive::tests::exact_arithmetic_and_errors`, `primitive::tests::comparisons_and_booleans` and `primitive::tests::table_signatures_and_currying_agree`.

## Native runtime assumptions

Native values synthesize their thunked curried signatures from [the native table](#native-prelude). Saturated operations check each argument against that same row and synthesize its result returner.

The kernel remains pure: it gains neither primitive syntax nor an arithmetic evaluator. The checker bridge admits each distinct native row present in the core arena as a named opaque axiom of its table signature, before the source module's declarations. Erasure turns a native value into that constant and a saturated operation into ordinary force and application nodes. Export retains these named assumptions, and a declaration's kernel audit reports the native constants it depends on. Kernel admission verifies types; it does not certify the host arithmetic implementation or introduce arithmetic equations into conversion. No unchecked admission is used.

**Choice.** Explicit, auditable runtime assumptions rather than silently skipping kernel admission or adding host arithmetic to the trusted kernel. Revisit when a certified arithmetic implementation can replace an opaque signature while preserving the runtime contract. The checker witness `bridge::tests::native_operations_cross_as_audited_assumptions` checks the exported axiom, reference remapping and audit.

## Nominal data and structural records

A `DataSignature` owns a parameter telescope, constructor field lists in tag order and a positive universe bound. `ValueType::Data` retains the declaration identity and term-valued arguments; `Value::Constructor` retains its full classifier, tag and ordered fields. Parameter classifiers bind their predecessors. Constructor fields see all parameters but do not bind one another. A `DataCase` motive binds one scrutinee; its branches are functions in the ambient context. Iterative rewrites preserve these distinct scopes.

Record types and values use ordered field maps. Labels identify fields, not offsets, and `RecordProjection` is a computation returning the selected value. All native children participate in syntax equality, rewriting and ownership; arities are not limited to three.

**Choice.** Dedicated native forms rather than abstract atoms or a structural sum/product encoding. Typed code parameters and value indices share term-valued slots; the checker keeps every slot invariant. **Reversal.** Certified definitional index conversion requires its own evidence reader. The current checker/kernel boundary and the named [parity floor](../core-checker/README.md#data-and-record-floor) are recorded together.

A field may name its own declaration's family: the syntax is an ordinary `ValueType::Data` at the declaration's own position, and whether that occurrence is admissible is the checker's question, not the arena's. `Computation::Fixpoint { body, evidence }` is `fix x. M`: its body stands under one intuitionistic binder, the self thunk, so binder rewrites, shifts and substitutions treat it as they treat a lambda. `FixpointEvidence` is the kernel's own, `Partial` or `StructuralDescent`; the arena records the claim and grants nothing, and syntax equality distinguishes the two claims.

## Native universe paths

`PathUniverse(a, b)` is the classifier `Path_U a b`; reflexivity, equivalence and product values introduce native paths, and `Transport` eliminates them. Certificates share the kernel’s portable `PathEvidence` vocabulary. Arena identity and content hashing retain evidence; `equal_certificate_syntax` compares raw classifier and map syntax while erasing evidence only. Computationally equivalent maps do not thereby identify certificates. Binder rewrites traverse classifier codes and translator bodies without reducing those maps.

**Choice.** Native syntax in the ordinary arena, rather than a second path arena with different traversal and ownership rules. Core syntax itself grants no admission authority: the checker validates the closed endpoint fragment and the kernel replays candidates. Element-identity, higher-field, bridge-mode and `Flow_U` programs remain separate kernel APIs. **Reversal.** Extending the code fragment requires corresponding formation, admission and replay rules, not a syntax-only permission.

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

A constructor records child ids supplied by its caller. Keeping those children live in the same arena, within the representable family-index limit, makes a same-family child strictly earlier than its parent; cross-family acyclicity follows from minting order rather than numeric comparison. The ids carry neither arena identity nor allocation generation. A lookup checks the current family bounds, not provenance: truncation removes nodes, but later allocation can reuse their indices. The caller therefore discards ids to removed nodes. `CoreArena::watermark` snapshots the four family lengths and `CoreArena::truncate_to` drops later nodes without growing a family when given a stale larger mark. Each walk over arena edges belongs to the consumer that needs it.

## One failure vocabulary

`FailureClass` lives here because this is the lowest crate both the lowering and the checker depend on: each classifies its own refusals with its own `const`, wildcard-free match, and a report groups both under one enum without either crate naming the other. The type carries no behaviour beyond its name; which refusal falls in which class is decided by the crate that owns the refusal. The alternative was a copy of the enum in each producer, kept equal by convention, which is two vocabularies a report would have to reconcile. Reversal: a producer whose failures need a class the others do not have, at which point that class is argued here rather than added in the producer.

## Specification attributes

Nontrivial operations carry executable `#[spec(...)]` predicates and `# Adequacy` hypotheses linked to runnable witnesses. The predicates observe allocation indices and family lengths, lookup identity, the selected context slot, and rewrite scheduling and reconstruction. `Context::open` and `Context::occurrence` capture only bounded entry state: depth and selected-slot observations are executable without cloning the context. Finite transition witnesses distinguish changes to neighbouring slots.

The choice is constant-size captures and local observations rather than whole-arena or whole-context snapshots, which would allocate and can turn a linear walk into a quadratic one. The variable rule checks the below/equal/above-depth boundaries, including saturated arithmetic and substitution beneath a binder. Independent level-based construction checks 600 deterministic bounded codomains; fixed asymmetric goldens constrain that reference observer, and the small-stack integration witness walks 50,000 static applications. These are scoped witnesses, not a proof of equivalence for ungenerated terms.

Run the crate with executable specifications enabled:

```sh
RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-core-term --all-targets
```

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
