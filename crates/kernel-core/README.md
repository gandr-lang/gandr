# gandr-kernel-core

The certified kernel's judgements: the defunctionalized checking machine, type formation, conversion, the admission choke point, the check memo wired as the default path on both machines, and the sequential replay of an untrusted engine's conversion trace.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Arithmetic and absence](#arithmetic-and-absence)
- [Memo binding conditions](#memo-binding-conditions)
- [Key derivation](#key-derivation)
- [Memo measurements](#memo-measurements)
- [Poisoned memo entries](#poisoned-memo-entries)
- [Staging order and admission](#staging-order-and-admission)
- [Sharing-aware conversion](#sharing-aware-conversion)
- [Dependent arrow and rewrites](#dependent-arrow-and-rewrites)
- [Universe families, codes and the lift](#universe-families-codes-and-the-lift)
- [Static operators](#static-operators)
- [Conversion replay](#conversion-replay)
- [Universe flows](#universe-flows)
- [Native universe paths](#native-universe-paths)
- [Identity and bridge recursion](#identity-and-bridge-recursion)
  - [Function identity and funext](#function-identity-and-funext)
  - [Native fibres and admission](#native-fibres-and-admission)
- [Guarded higher fields](#guarded-higher-fields)
- [Recursive code observations](#recursive-code-observations)
- [Sharing and persistence](#sharing-and-persistence)
- [Mutation findings](#mutation-findings)
- [Specification attributes](#specification-attributes)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `Environment` admits declarations through one checked choke point, `add_decl`, and one warned bypass, `add_decl_unchecked`; `audit` reports what an admitted declaration transitively rests on. Beneath the choke point sit a bidirectional checking machine, a type-formation walk that computes a type's universe level, and structural conversion. Beside it, `replay` rechecks a term-conversion verdict an untrusted engine reached, decision by decision, from the trace that engine recorded. Representation, the sharing format and the decode budgets belong to `gandr-kernel-term`, the universe algebra to `gandr-kernel-strata`, the memo's storage to `gandr-kernel-check-memo`, and the decision vocabulary to `gandr-kernel-conversion-trace`; this crate is what re-derives an obligation.

**Why.** The kernel grants a producer no credence: every declaration is re-checked before admission, including one a decoder built from untrusted bytes. Such a term can be arbitrarily deep and heavily shared, so the checker must be total on adversarial depth and must not pay for a shared subterm once per occurrence.

**How.** The checker is a defunctionalized machine over a goal register, a produced register, a heap frame stack and an explicit typing-context stack, never mutually recursive methods bounded by a depth budget, so it is total on depth. The arm-by-arm correspondence table in the `check` module docs is the trusted-base audit artifact: a reviewer walks it to confirm the machine is the judgement. Conversion is structural comparison with a positive-only id-equality fast path: equal ids discharge a pair, unequal ids decide nothing. Both machines consult a check memo keyed by content, so a shared subterm is checked once per distinct support, and the memo lives for one check call. Admission truncates the arena on both verdicts, clamped at the admission floor so a rollback never deletes committed content.

## Provided features

- **Admission.** `Environment` with `stage`, `add_decl`, `add_decl_unchecked`, `abandon` and `audit`; `StagedDeclaration`, `CheckedId`, `AdmittedDeclaration` and `AxiomReport`. The arena is truncated on both verdicts: to content-end on success, to the declaration's content-start on rejection, clamped at the admission floor.
- **The checking machine.** `check_declaration`, the default path with a fresh memo, and `check_declaration_with_memo`, the opt-in entry that returns a verdict and never a `CheckedId`. Checking is bidirectional and annotation-free.
- **Type formation.** An iterative walk computing a type's universe level, gating lift strictness, level scope, a sealed atom's kind, and the code a decode of either family owes.
- **Conversion.** `convert_value_type`, `convert_comp_type` and their `convertible_*` forms: structural comparison of two types, descending into the terms they carry, over `Convertibility`.
- **Conversion replay.** `replay`: a conversion trace replayed against an engine's `EngineClaim` for two `ReplaySides`, unfolding only what `Unfoldings` defines and stopping at a `ReplayBudget`, answering a `KernelVerdict` — certified convertible, certified not convertible, or declined with a `ReplayDecline`, whose `ReplayRefusal` names the `TracePosition` that did not replay.
- **The content key.** `ContentTable`, `encode_support`, `content_digest`, `NodeSupport` and `SupportContext`: content ids, canonical support encodings and their digests.
- **The rewrites.** `shift_value_type` and `substitute_comp_type`, de Bruijn shifting and substitution as memoized machines.
- **Accounting.** `ExpansionCensus`: goal expansions and memo recalls per plane, the observation every measurement here is asserted through.
- **Errors.** `KernelError`, whose payloads are content — a head former and the offending node's content digest — because admission truncates the arena and an arena id would dangle.

## Expected features

- **Staging discipline.** A producer resolves every staged declaration by admitting, bypassing or abandoning it. A staged declaration left unresolved keeps its content in the arena and blocks the admission of every declaration staged before it (see [Staging order and admission](#staging-order-and-admission)).
- **A vouched bypass.** `add_decl_unchecked` performs no checking: the caller vouches for the declaration, a wrong one can make the kernel prove anything, and `audit` reports every declaration that rests on it.
- **A trace in the kernel's terms.** A replay's caller translates its sides and the bodies it allows unfolding into the replay's arena, maps each trace identifier to the constant it names or `ReplayNode::Other`, and maps its engine's verdict to an `EngineClaim`. A body is a closed value, an operator's body is closed beyond its parameters, and a constant given neither is opaque.
- **Reduced codes.** Conversion fires no reduction, so two codes convert only when they are structurally equal. A producer hands the kernel reduced codes to avoid a refusal.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Stage a declaration, admit it, watch an ill-typed one refused, and audit what the admitted one rests on.

```rust
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::LevelSignature;

fn example() -> Result<(), KernelError> {
    let mut environment = Environment::new();

    let unit = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let admitted = environment.add_decl(unit)?;

    let ill_typed = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_base(BaseType::Integer);
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    assert!(environment.add_decl(ill_typed).is_err());

    let report = environment.audit(admitted);
    assert!(report.axioms().is_empty());
    assert!(report.unchecked_admissions().is_empty());
    Ok(())
}
```

`tests/acceptance.rs` carries the memo measurements and the poisoned-entry cases; `tests/adversarial_depth.rs` the depth totality. Run them with the unit tests, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-core
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-core
```

## Arithmetic and absence

Arithmetic uses [quenchant-arith](https://github.com/gandr-lang/quenchant/tree/111850988c96b7b33ee898f54c017ca645243e7f/crates/quenchant-arith): strict operations for counts bounded by allocated data or a preceding guard, wrapping multiplication only for FNV-1a modulo 2^128, and saturation only for the stated census ceilings, binder-index ceilings and conservative context reach. Defaults, unsafe `fast` mode and optional instrumentation remain off. The alternative was primitive arithmetic with profile-dependent overflow behavior or a local copy of these families; one maintained implementation gives each operation an explicit, profile-independent meaning. Reconsider when the arithmetic domain changes or a published release replaces the shared source pin.

Non-failure absence uses [quenchant-shape](https://github.com/gandr-lang/quenchant/tree/111850988c96b7b33ee898f54c017ca645243e7f/crates/quenchant-shape), with a sealed reason enum at each decision site rather than an undifferentiated `Option`. A failure remains a typed error, never a fabricated value. The six sites distinguish a formation answer from a term answer, an out-of-scope slot, an unbound variable, an unadmitted constant, a substitution needing no carrying shift, and a goal without an expected type. Reconsider a reason only when its caller gains a distinct response to it; container lookups and external traits retain their own boundary types.

Content numbering remains zero-based and infallible. Every fresh record first appends a nonempty framed image, so the count is bounded by the allocated byte stream. Supported targets bound that allocation by `isize::MAX`, below `u64::MAX`. The latter ceiling is not an observable state; a test that installs an impossible private count would test another state space. The enforcing specification checks the count/stream bound, and the existing content-collapse and sharing witnesses exercise both fresh and reused records. A fallible mint was rejected: it adds an unreachable error, and neither silent diagnostic failure nor a change to one-based numbering has a semantic justification. Revisit the boundary if content numbering stops being backed by this in-memory stream or target widths exceed 64 bits.

## Memo binding conditions

The seam crate names no term type, so everything that makes a memo sound is a consumer obligation, and this crate is the consumer. Six conditions bind it:

| condition | discharged by |
| --------- | ------------- |
| static dispatch on a null-object seam that compiles away | `check_declaration_with_memo` is generic over `CheckMemo`; every interaction sits behind `matches!(M::ACTIVITY, Active)` |
| the public admission entry cannot reach the opt-in entry | `Environment::add_decl` takes no memo and builds its own; the memo-taking entry returns a verdict and never a `CheckedId` |
| a lifetime of one check call | `check_declaration` builds a memo and a session and drops both; a support is meaningful only against its own session |
| the content-only key | `(direction, obligation content, expected content, telescope content)` — no arena id, no allocation order |
| storage and policy outside the kernel crate | the seam crate owns the table and its ordering; this crate holds a type parameter |
| no authority and no persistence in a hit | a hit claims only that this process already computed this answer for this support |

The key carries no arena id, so dangling ids are not why the memo lives for one call. The lifetime rests on the two-wall discipline directly: a hit claims only its own history, and no kernel-checked support discipline exists. An outcome also carries arena ids even though the key does not, so an entry outliving its arena would hand back a type that no longer resolves.

## Key derivation

Content is named by a content id, assigned by interning each node's one-level record — its tag, its inline payload, and its children's already-assigned ids — bottom-up and exactly. No hash decides an id. The digest above it is a positive fast path only: different digests prove disagreement, equal digests hand off to byte equality of the canonical support encodings, and a collision costs one comparison and degrades to a miss.

Only the binder slice a node can reach enters its support, folded in telescope order. `LooseDepths` computes each node's reach bottom-up and widens to the whole context where it cannot answer, so a defect here costs collapse and never manufactures a hit.

Four trap pairs carry injectivity of the record encoder rather than randomized testing, because key collision is the one obligation a randomized differential cannot probe: two field orders, two families sharing a payload, signed zeroes, and a length-prefix ambiguity.

Each distinct node is encoded once per session, so deriving every key of one check costs one pass over the distinct nodes — linear even on a chain-deep term a decoder built from bytes. What the content key buys over an identity key on a real corpus is unmeasured; a measurement showing that pass dominating the reuse payoff re-keys the memo.

## Memo measurements

The self-similar composite is `t_0 = ()`, `t_{k+1} = (t_k, t_k)` against `T_0 = Unit`, `T_{k+1} = T_k x T_k`. The collapse law is asserted as a closed form at three depths, decomposed per plane.

| depth | memoless total | memoless term | memoless type | memoized total | memoized term | memoized type | collapse |
| ----- | -------------- | ------------- | ------------- | -------------- | ------------- | ------------- | -------- |
| 8 | 1,278 | 767 | 511 | 19 | 10 | 9 | 67x |
| 12 | 20,478 | 12,287 | 8,191 | 27 | 14 | 13 | 758x |
| 16 | 327,678 | 196,607 | 131,071 | 35 | 18 | 17 | 9,362x |
| 28 | 1,342,177,278 | — | — | 59 | 30 | 29 | 22.7M x |

Memoless is `5 * 2^d - 2` in total: `3 * 2^d - 1` body checks against `2^(d+1) - 1` type formations. Memoized is `2d + 3`: `d + 2` term supports against `d + 1` type supports. The depth-28 row is measured at the public choke point: a definition whose tree expansion is 1,342,177,278 goals admits checked through `Environment::add_decl`, with no bypass. Its memoized columns are asserted through the opt-in entry on the same shape; its memoless columns are the closed form's value and are never run.

**Anti-vacuity.** The memoless term-plane law pins the occurrence count, so the workload cannot stop being shared unnoticed. The memo's entry count is compared against the census from the other direction, per plane and in total. A separate case pins that the shared composite and its fully unshared spelling cost the memoless checker identically: sharing buys checking nothing without the memo.

**Edit locality: `d + 1` node checks per depth-`d` edit,** measured within one check call. Both spellings are checked in one pass, because warming a memo on the original and reusing it across calls would measure exactly what the lifetime rule forbids. Extra term-plane expansions are 9 at depth 8, 13 at depth 12 and 17 at depth 16; the type plane adds nothing, because the edit changes no type. The count is `d + 1` rather than `d + 2` because of the content key: the edited leaf's freshly minted payload collapses with the original's.

**Adversarial depth.** A 20,000-link `thunk`-over-`return` chain checks totally inside a 256 KiB stack at both memo instantiations, costing 40,002 term-plane expansions. The count is asserted, so the case cannot degenerate into a shallow term and keep passing.

## Poisoned memo entries

Each case is a permanent suite member, in both directions and on both planes, and asserts its exercised-path count through the expansion census:

- a poisoned term entry turns a refusal into an acceptance (served once);
- an entry differing only in its binder component is not served (served zero times), with a positive control under the matching telescope that does change the verdict, so the case measures the binder component rather than an inert poison;
- a poisoned type-formation entry turns an admission into a universe-violation refusal (served once, on the type plane);
- a term-shaped answer in a type-formation support is declined and recomputed at exactly the cost of having had no entry, and the mirror case holds on the term plane.

## Staging order and admission

A staged declaration outlives its builder's borrow, so staging order need not be admission order. The admission floor absorbs one shape of divergence, and admission refuses the other.

**Content-start below already-admitted content** is absorbed. A rejection clamps its rollback into `[floor, content-end]`, so it never deletes committed content and never leaves an intermediate behind; the rejected declaration's own nodes stay as unreachable orphans. Retaining garbage is the failure that trades for deleting evidence.

**Content-start below outstanding content is refused.** Stage one declaration, stage a second, then offer the first: the second's nodes sit above the first's content-start while its `StagedDeclaration` is live, the floor lies below both, and a contiguous truncation cannot spare a disjoint region. Rolling back would hand the producer dangling roots, or free indices a later staging re-mints so that a subsequent admission checks other content under that name. The environment tracks the content-start mark of every staged, unresolved declaration and answers `KernelError::OutstandingStagedContent`, naming how many sit above.

A mark is resolved by admitting, bypassing or `Environment::abandon`; abandoning a staging session before it finishes resolves its mark too. `abandon` truncates when nothing outstanding sits above the mark and otherwise retains the region as an orphan, the same clamp a rejection takes. "Above" is componentwise rather than lexicographic, because truncation is per family.

## Sharing-aware conversion

Conversion carries a per-call set of discharged pairs. Without it, two roots that share a subgraph re-walk every shared pair once per occurrence, so the work is the expansion of the compared graphs rather than their size — exponential in sharing depth on a term a decoder handed over. A pair discharged once stays discharged: over this vocabulary a type pair's verdict is a function of the two nodes alone, and any pair that fails returns immediately, so nothing is recorded as discharged while its own subtree is undecided. The set holds only pairs, creates no sharing, is consulted for nothing but skipping a repeat inside one comparison, and dies with the call.

The set bounds the conversion path rather than decoding, so it sits outside the four amplification budgets of `gandr-kernel-term`. It guards a public surface — a direct arena caller is not behind the decoder's expanded-work gate — and it has no extensional face.

No reduction fires: two codes convert when they are structurally equal, which is sound and incomplete.

## Dependent arrow and rewrites

The dependent arrow forms at the join of its children like the non-dependent one, and a lambda checks against it through the domain slot its codomain is written against. What makes it dependent is the universe-decoding former: a type read off a code, a value whose type is a universe, and the only former whose child crosses from the type language into the term language.

**The carried level keeps the two machines apart.** The former names the universe it is read out of, so type formation is a lookup rather than an inference, and the obligation formation cannot discharge — that the code inhabits that universe — is recorded rather than pursued. The driver drains the record through the checking machine, and a drained check that owes further codes appends to the same worklist. Neither walk calls the other, so the recursion ban is met by the architecture rather than by a depth budget. The drain carries a ceiling derived from the format's subterm-table cap, because a drained check can form a synthesized type and owe more codes, so the loop's bound is not the artifact's own size.

**The two de Bruijn rewrites are machines.** Shifting raises every free index at or above a cutoff; substitution replaces the innermost binder's variable and lowers everything outside it. Both are loops over an explicit task stack and an explicit results stack, so they are total on a term a decoder built from bytes, and each is memoized at its own instantiation of the check-memo seam, so a shared subterm is rewritten once. Carrying a replacement under a crossed binder is a shift, scheduled as a task on the same stack.

Five sites in the checker consume them. A variable synthesis raises its context slot past the binders between the slot and the use site, and an application at a dependent head instantiates the codomain at its argument. **A type keeps the scope it was written in**: a plain arrow's codomain is written outside the arrow's binder, as formation and the reach walk read it, so a lambda checked against it raises the codomain past the slot it pushes, and a bind or a case raises its expected type past its binder the same way. A type synthesized under the binder of a bind or a case branch is strengthened back out of it: the binder's variable is instantiated at the index one past the outer context, which nothing outside the binder can name, and the reach walk refuses the result as `BinderEscape` when that index survives — exactly when the type mentioned the bound value. A dedicated occurrence walk would answer the same question as a third machine; the instantiation and the reach walk already answer it, so it would duplicate both. While every type was closed each of these steps was the identity, which is how the plain arrow's lambda rule could once share the dependent arrow's.

Shifting a value type and instantiating a computation type are the public rewrite surface; the other family faces are crate-visible. A type carrying no code rewrites to itself and the walk hands back the node it was given, so the common case costs nothing and the sharing a decode preserved survives.

**The audit follows codes.** A declaration's type reaches another declaration two ways — a sealed atom names one directly, and a code names one through the term language — and the trust report would miss the second if it followed only the first. A quote crosses back, so the one walk behind both sets follows a value into the type it quotes as well as a type into the code it decodes. The sealing-provenance set does not follow codes: it asks which sealed atoms a projection rebound, and widening it would make the gate more permissive on the one surface whose job is to be falsifiable.

## Universe families, codes and the lift

**Two universes, one rule.** The universe of value types and the universe of computation types each form one level above the level they carry, as value types: a code is a value whichever family it decodes into. A sealed atom's kind must be the value universe, because an atom is a value type. A quote synthesizes the universe of its family at its quoted type's own level, by calling the formation walk directly, as the lift's frame does; the computation decode owes its code against the computation universe exactly as the value decode owes its code against the value universe, through the same deferred obligation.

**No cumulativity; the lift is written.** A code inhabits exactly the universe at its type's level, so a code bound for a larger universe reaches the kernel as the quote of an explicit `Lift`, and the formation walk's strictness check on that lift is the kernel's smallness check. The producer decides smallness at the site it checks and writes the lift at readmission; the kernel trusts neither the decision nor the level. The alternative, a cumulative universe rule in conversion or in checking, would make conversion directional and put subtyping into the trusted base; the reversal condition is a measured cost of the written lifts that a subsumption rule would remove.

**Codes compare by their quoted types.** Structural conversion compares two quotes by the types they quote, and the replay closes a comparison of two codes as the untrusted engine's shared comparison does: α-equal codes convert, codes whose quoted types hold nothing that could still unfold are apart, and any other pair is refused rather than guessed at. Rigidity reads through quoted types and the codes they decode, so the engine's verdict of apart is one the kernel reaches in its own terms.

## Static operators

**Formation.** A static Pi forms only over static classifiers — a universe of either sort, or a static Pi — and refuses any other child as `StaticClassifierExpected`. It forms at the join of its children's levels and is a value type, so an operator is a value whatever it builds. The check reads each child's head; a static Pi child is formed by the walk in turn, so every leaf of a curried classifier is reached.

**Application.** A static application synthesizes: its head synthesizes a static Pi, its argument checks against the domain, and it produces the codomain, which binds nothing. A head of any other type refuses as `ValueShapeMismatch` expecting a static Pi. Every static application the kernel admits is neutral: there is no static lambda for it to meet. Structural conversion compares two static applications head to head and argument to argument, and a static Pi by its two children.

**δβ in the replay.** A static definition's certificate unfolds one instance of an operator. `Unfoldable::Operator` hands the replay the operator's body with its `ParameterCount` binders stripped, the innermost binder its last parameter; unfolding a value headed by it instantiates the binders at the side's first arguments, innermost first, each argument shifted past the parameters still standing outside it, and keeps any further applications over the reduct. A body standing at a static spine keeps the spine. An operator short of its arguments has no reduct and refuses as unreadable.

**Alternatives.** A static lambda in the kernel would turn this δβ into a δ-step followed by a β-rule at values, owing a reduction the kernel would otherwise never fire; stripping the binders keeps the substitution the kernel already trusts for computations as the only rewrite. A dependent static Pi would need a substitution at every synthesis; no former at this vocabulary is indexed by a static argument.

**Reversal.** A kernel static lambda arrives with an operator exported across a module boundary (see `gandr-kernel-term`); then the operator unfolding becomes a body unfolding, and the replay's weak head form fires static β like the computational one.

## Conversion replay

Term conversion with δ-, β- and η-rules is proof search, and a concurrent search is too large to trust. Courant and Leroy (§9 of "A Lazy, Concurrent Convertibility Checker", POPL 2026, `doi:10.1145/3776695`) instrument their checker to emit a trace of its decisions and recheck the trace sequentially. `replay` is that recheck: the engine's search stays outside the trusted base, and what the kernel trusts is a loop that fires every step itself and reads the trace only where a rule leaves a choice.

**Choice.** Every goal carries the verdict its derivation owes. Both sides are put in weak head form by the reductions that need no choice — β, a forced thunk, a returner met by a bind, an injection met by a case — and then exactly one rule row applies. A `ComparedShared` closes the goal when the sides are α-equal, or rigid and α-distinct, rigid meaning nothing inside can reduce. A defined head takes a δ-decision: `Unfold` with the reduction naming its side, after an optional `Postpone` naming the other side's head, or `Freeze`, or `ConstShortcut` over two applications of one constant. A thunk against a thunk or a neutral takes two `Force`s, and a lambda against a neutral takes `EtaExpand` on the neutral side. Every other goal is structural and reads no decision: a leaf decides it, a convertibility derivation pushes all its premises, and a refutation reads the `NegativeSubgoal` naming the one premise it rests on. Under a refutation, `Freeze` and `ConstShortcut` are refused outright: a frozen pair or a shortcut that fails proves nothing about the unfolded terms, so only the unfolding branch refutes. A `ComparedShared` met at a decomposable goal closes that goal when it can and otherwise passes to the first premise; the engine emits an agreeing decomposition it settled equal as that one closing, so the two readings coincide.

**Three verdicts.** The replay certifies convertible or not convertible only when the trace replays as a derivation of the engine's claim, every decision used and none left over. Everything else declines: the engine's own decline, a budget the replay ran out of, or a refusal naming where the trace stopped applying. A schedule that starved the engine of the turns its answer needed is such a decline, and the kernel has no search of its own to recover it with. A decline is never read as a refutation, so a wrong or unlucky engine costs completeness and never soundness. Every step is charged to the budget, which bounds a long trace and a term that reduces forever alike, and the reducts the replay mints are truncated away before it returns.

**Alternatives.** Running the engine's search inside the kernel would certify by trusting the search. Trusting the engine's verdict would certify nothing. Replaying a refuted decomposition without its negative subgoal means trying every premise, which is search. Memoizing replayed sub-derivations would let a trace refer back to a shared one; the engine emits a derivation shared by two parents once under each, so the trace is the derivation's expansion as a tree and the replay needs no table.

**Reversal.** A back-reference decision, with a replay-side table keyed on the goal it names, replaces the expansion once a measured trace of a deeply shared proof outgrows the replay budget. A closing the kernel cannot reproduce, because the engine's structural equality and the kernel's α-equality disagree on a pair, shows up as a refusal on an engine trace and moves the tie-break into the vocabulary.

**Laws and evidence.** The unit and purity specifications, their named witnesses and the goal-refinement composition shape live on [`replay`](src/replay.rs). `KernelVerdict` carries the refusal class table and the certified fragment's partial-equivalence scope. [`tests/replay_laws.rs`](tests/replay_laws.rs) generates 256 recipes, checking each claim twice and in a cloned arena, with exact unit-law goldens and rollback checks.

**Property-test dependency.** Dev-only `proptest` uses the workspace's 1.11 version range, defaults off and only `std` for generation, shrinking and persistence. It reuses the workspace's runner without expanding the shipped kernel dependencies. QuickCheck would add a second runner; hand-written enumeration would lose shrinking of generated term recipes. Reconsider on an unmaintained release, a high-risk advisory or a need the existing strategy API cannot express.

## Universe flows

`flow_universe` defines a separate in-memory `Flow_U a b` family over quoted Unit, Sum, Product and Base codes. A forward certificate stores one closed CBPV translator and one proposed image/dialogue per source constructor pattern. It carries neither an inverse nor round-trip evidence. Every consuming formation checks the translator in a fresh closed checker session, validates the images, and replays kernel-built positive claims. No stored node or classifier is an admission receipt.

| Boundary | Rule or refusal |
| -------- | --------------- |
| Forward formation | Exhaustive symbolic source patterns; each target Base position selects a same-typed source leaf. |
| Directed computation | `ride e v` exposes the checked forward application for ordinary conversion replay. |
| Directed reflexivity | `ride (stay a) v` returns `v` in one step, without allocating or evaluating an identity translator. |
| Motive formation | Moving endpoints occur only covariantly; arrow domains and Flow sources reverse variance. |
| Symmetry | `Flow(Moving, Fixed)` returns `NonCovariantMotive`, including when nested beneath positive formers. |
| Family separation | A valid equivalence at a Flow boundary, or a Flow at a Path boundary, returns `FamilyMismatch`. |
| Sequential composition | `Compose { seam: Sequence, .. }` checks the intermediate type and lowers in order to CBPV bind. |
| Feedback | Connecting the second output back into the first input returns `Cycle` with both occurrences. |

**Native family boundary.** `Certificate::Path` carries a native value id. `form_certificate` synthesizes that value through the ordinary closed checker and decodes its checked `Path_U` endpoints; there is no auxiliary path arena or trusted classifier shortcut. Missing round-trip evidence and non-path classifiers refuse. Matching Path and Flow families retain separate formation judgements, and both cross-family directions refuse before elimination. The Flow range in the [wire-tag table](../kernel-term/src/tags.rs) remains reserved and unassigned.

**Leaf naturality.** Each source Base position is a distinct rigid variable, including equal-typed positions in a product. Proposed output syntax contains only canonical constructors and those correctly typed variables. The kernel replays the translator on these symbolic inputs; a trace generated at a literal sample has no authority over that obligation. Literals nested beneath sums or products, fresh variables, wrong-typed selections, and sample-only constant maps refuse. The witnesses cover diagonals, both injections, codiagonals, product identity and terminal projection to Unit. The inherited native CBPV vocabulary has no general product eliminator, so these witnesses do not establish generation of every projection or fullness of the one-way alphabet.

**The gate reads wiring.** Sequence has one edge between two occurrences; feedback adds the reverse edge and closes a cycle. Equal endpoint codes do not identify occurrences. In particular, injection followed by fold forms and replays as identity, and terminal followed by injection forms a constant Bool endomap. Neither composite grants inverse evidence. This closed-code gate handles explicit two-occurrence seams, not a general reflected cell-support graph or invertible-core comparison.

**Choice.** The rule arena reuses native closed checking and conversion replay. Flat, constructor-ordered ids and bounded iterative walks avoid recursive ownership; formation and lowering tables live only for one call. Reusing native replay avoids a second evaluator; host-language translators would bypass the obligation. Native persisted formers would require encoding, support and wire integration. No wire tag is allocated. Reconsider this representation when declaration admission must consume Flow syntax. Motive checking is the term-structural covariance side condition over El, Flow, Arrow, Sum and Product; value transport uses `El(Moving)`. General dependent directed elimination and the reflected variance calculus remain outside this rule language.

The seven `flow_universe::tests` witnesses use the independent conversion engine and exact expected outputs. The public replay boundary restores its arena watermark on success and failure. Its memo discipline is the existing six-condition discipline: no caller-supplied checker memo, persistent verdict, storage policy or authority-bearing hit.

**Mutation scope.** The universe-flow source range owns a standalone campaign over leaf aliasing and type confusion, manufactured constants, omitted source coverage, forged dialogues, reversed composition, missed feedback, motive sign propagation, family coercion and Stay reduction. No mutation campaign or score is claimed.

## Native universe paths

`ValueType::PathUniverse(a, b)` forms `Path_U a b` over closed quoted Base, Unit, Sum and Product codes at level zero. `Value::PathEquiv`, `PathRefl` and `PathProduct` introduce paths; `Computation::Transport` is their only eliminator. They participate in ordinary arena traversal, declaration admission, structural conversion and artifact encoding. The surface parser has no path syntax.

| Rule | Kernel obligation or computation |
| ---- | -------------------------------- |
| Formation | Both endpoints decode to closed first-order value types. |
| Equivalence | Closed translators check at opposite CBPV arrows; every source and target round trip replays. |
| Reflexivity | The endpoint code forms. |
| Product | Both component paths form; endpoints are their products. |
| Transport | The input checks at the source and the comparison target at the target returner. |
| Equivalence beta | `transport (equiv f g) v` becomes `force f v`. |
| Reflexivity beta | `transport (refl a) v` becomes `return v` in one step. |
| Product beta | Pair input becomes left and right component transports. |
| Path conversion | Codes and translators compare structurally; round-trip evidence grants no certificate equality. |

Round-trip coverage is symbolic: sums enumerate both injections, products enumerate constructor combinations, and Base leaves introduce distinct rigid variables rather than sample literals. Each pattern requires a dialogue. Missing, extra or invalid evidence refuses admission. A shape/coverage ceiling and per-dialogue replay budget are independent limits, not one global work counter.

`Dialogue::pair` constructs one product dialogue by prefixing explicit `Decompose` decisions for the returner and pair, then concatenating component traces. This prevents an initial `ComparedShared` from consuming a component trace at the enclosing pair. The kernel re-derives every boundary and premise. There is no transitive certificate-composition operation.

`Environment::add_decl` checks both endpoint codes, checks translators under an empty term context and replays every source and target round trip. Decoding and frontend typechecking grant no authority. Portable evidence participates in artifact content and admission memo keys, but structural certificate conversion erases evidence only: it does not normalize translator syntax. A fresh admission owns the memo and rechecks imported candidates.

The seven witnesses in `path_universe::tests` submit native declarations and use independent `core-nbe` dialogues for Bool negation, product transport, reflexivity, wrong-answer refusal, non-equivalence refusal, intensional certificate conversion and absent K. The K witness applies ordinary force and case eliminators to a path and observes their typing refusals; it is not a theorem about future language extensions. Triple negation retains its two sequencing seams and is compared with direct composition at both Bool constructors.

`path_universe::code`, `Dialogue::pair` and `replay_transport` remain callable. Path operands are ordinary `ValueId`s in `TermArena`; no separate path arena or string-named eliminator dispatcher exists. `replay_transport` rechecks the native path and transport goal before consuming its dialogue.

**Choice.** Native syntax makes the ordinary admission boundary authoritative and permits artifacts to carry untrusted candidates. Transport reduces to ordinary CBPV computations; product transport sequences component computations through capture-avoiding binds. Rust translator closures or an auxiliary path arena would evade persisted admission. **Reversal.** Extend the code grammar only with formation, coverage and replay rules for the new fragment. Element identity, open codes, higher fields, function codes and general dependent elimination remain outside this fragment.

**Mutation scope.** Native formation, replay, structural conversion and encoding own a campaign over omitted coverage, swapped maps or product legs, accepted bad dialogues, reflexivity reduction, evidence omitted from memo keys, and translator syntax erased by conversion. The witnesses distinguish these observations; no mutation score is claimed.

## Identity and bridge recursion

The `identity_recursion` module folds a closed code vocabulary with `Mode::Identity` or `Mode::Bridge`. Identity also reaches the level-zero value universe, including occurrences beneath the admitted formers. It is an in-memory rule language beside `path_universe`, not persisted element-identity syntax. Endpoints are ordinary typed values in an open context; unsupported codes are refused before interpretation.

`Interpretation::path` consumes an ordinary native `ValueId`, synthesizes it through the declaration checker’s closed-value boundary and decodes the checked `PathUniverse` classifier. Native typing failures retain `KernelError` inside `RelationError::Typing`; endpoint failures retain `PathError`. No auxiliary path arena or formation cache participates.

| Code | Relation clause | Identity structure |
| ---- | --------------- | ------------------ |
| Unit | Unit fibre at every pair of indices. | Unit witness; reflexive transport returns its input. |
| Base | Discrete relation: identical indices give Unit; distinct canonical literals give Empty; unresolved neutral equality remains a relation. | Reflexivity is constructive; distinct variables are not assumed unequal. |
| Sum | Matching injections recurse on their payloads; different injections give Empty. An unknown injection remains suspended. | Payload reflexivity and transport use the matching branch. |
| Product | Component relations paired, including projections of neutral indices. | Componentwise reflexivity and composition; neither coordinate is dropped. |
| Thunk `U (A → F B)` | Suspended product `Π a₀ a₁. Rel(A,a₀,a₁) → Rel(B,force f a₀,force g a₁)`, with the same mode on both premises. | Higher-evaluation reflexivity and pointwise introduction; application transport replays both returners. |
| List A | Lazy constructor relation; each Cons applies the already-folded element clause and delays its tail. | A complete finite observation records Unit or a distinguishing Empty fibre, depth and instruction count. |
| Value universe at level zero | Identity only: native `PathUniverse` of the two indexed codes. | Native path reflexivity and certified translator replay. |
| `PathUniverse` | Identity only: the higher record of two native certificates. | Pointwise forward/backward fields and both round-trip coherence obligations, observed separately. |
| Abstract | Named interface obstruction, even for the same nominal atom. | Its declaration supplies a kind, not relation, reflexivity, transport and coherence fields. |
| Codes | Identity consumes existing `Path_U` formation; bridges are checked indexed families over two element types. | Existing certified-equivalence and transport semantics are reused, not redefined. |

**Base choice.** These built-in scalar codes are discrete; their canonical data has decidable equality. This is not a nominal-identifier test for sealed values. A different base interpretation needs an explicit relation interface. A sealed Abstract likewise needs a supplied relation, reflexivity, transport and coherence structure, with any bridge interpretation supplied separately. Looking through the seal or treating its name as equality evidence is not an alternative.

`Relation::constant` and `Relation::cases` construct heterogeneous indexed bridge families. The distinguishing witness is `Br_U Unit Bool` with fibre Unit at `((), inl ())` and Empty at `((), inr ())`. These direct first-order families require neither equality on arbitrary elements nor an equivalence. An arbitrary span needs endpoint fibres and reindexing laws before it can supply such a family. The implementation does not establish the full model laws of [Internal Parametricity, without an Interval](https://doi.org/10.1145/3632920). Bridge mode shares the code clauses but grants no automatic reflexivity or identity transport.

Identity evidence checks against its computed fibre. `reflexivity` constructs the diagonal; `compose` transports in the first-order identity fibre, pairing both product components. `transport` accepts native representable level-zero motives and reduces structural reflexivity to the exact input. An unresolved non-reflexive transport retains its endpoints, proof, motive and input as a neutral operation, not a fabricated target value. Suspended sum reflexivity is a structural diagonal program. This relation module does not provide J, arbitrary dependent motives, a general fibrancy theorem or an unrestricted universe hierarchy.

**Universe boundary.** The clause at a quoted `U₀` lowers to the existing native `Path_U`, subject to that former’s closed first-order endpoint stratum. It never interprets two code values as discrete syntax equality. Its diagonal is `PathRefl`; arbitrary evidence is checked as a native path, and code transport uses `path_universe::replay_transport`. Equal endpoint codes do not make a negation certificate reflexive: generic dependent transport stays neutral unless its proof is structural reflexivity. Generic first-order composition refuses code-level certificate composition with `CertificateOperationRequired` rather than replacing the composite by reflexivity. Explicit native certificates remain usable as evidence.

At a quoted `PathUniverse`, the same fold yields a certificate fibre. `Fibers::certificate` reuses `higher_field::unfold`, exposing the four existing obligations without deciding them. Lowering this record to a native first-order type returns `HigherFieldRequired`. This is the stopping point, not a claim of infinite coherence. Nested universe bridges, higher universe levels and an extensional conversion rule are not introduced.

**Universe choice.** Reusing the native former keeps path checking and replay authoritative; a second equivalence arena or discrete comparison would erase the certified map. **Reversal.** A broader native endpoint stratum or a checked certificate-composition language can expand the clause without changing its interpretation.

### Function identity and funext

At a thunk code, the fold records argument and result relations without comparing functions. `apply_related` checks two independently supplied arguments and their relation evidence. It crosses each `U` seam with `force`, applies the function, and relates the values returned through `F`. A variable or stuck application retains a function fibre and both application computations. It never becomes Empty because evaluation is stuck.

`HigherEvaluation` is an untrusted introduction: each component contains two claimed returned values, their `core-nbe` dialogues, and an inhabitant of the computed output relation. The kernel constructs every replay claim itself. Open component telescopes close under lambdas before replay. `function_reflexivity` replays the same function on related inputs; ordinary structural `reflexivity` requires this higher introduction at function fibres. `funext` stores raw evidence in `Identity`, and every consuming operation checks it again. Native conversion gains no function-extensionality rule.

Universal introductions cover closed functions with first-order arguments and native-representable output fibres. Coverage uses Unit, matching Sum injections, Product combinations and fresh rigid Base variables; the relation premise identifies each discrete Base pair, without sampling literals. Higher-order argument coverage and higher-order output evidence remain suspended; their quantified function fibres still form. The admitted function code is the non-dependent arrow `U (A → F B)`; dependent arrows, universe and recursive codes are outside this clause.

`transport_application` instantiates a checked function identity at an argument diagonal and computes the related returned values. Other native motives retain `Transport::Neutral`, including non-reflexive function identities. The Bool witnesses compute `not ∘ not = id` at both constructors and reject `not = id` with the failing component. Double negation uses the annotation-free, case-inlined term with its return/bind seam; the independent engine checks the direct composition too.

**Higher-evaluation cost.** Each Boolean introduction has two components and four application replays. Coverage and each replay have separate finite allowances; implicit beta steps consume replay budget even when they emit no decision. Product coverage can grow multiplicatively, so these bounds do not establish a global work theorem. Traces move into identity evidence; only a retained neutral transport clones that evidence to own its suspended computation.

**Function choice.** A lazy related-input product preserves the observational definition, including distinct related Unit arguments. Native function conversion would impose a stronger equality test; finite literal sampling would not establish the universal premise. Replaying ordinary CBPV evaluation reuses the existing trusted machine. **Reversal.** Higher-order introductions require a quantified evidence language that checks relation assumptions and nested function evidence; complete dependent funext additionally requires its substitution and fibrancy laws.

### Native fibres and admission

Computed fibres lower to native Unit, Empty, Product and universe-path types. Empty forms at level zero, has no constructor, and `absurd e` checks against any expected computation type when `e : Empty`. It has no beta rule. Empty is an output fibre here, not an additional input code in the fold’s closed vocabulary. As an ordinary native leaf it remains a legitimate bounded-alias target.

The arena handles remain scoped to their original nodes; callers must not truncate and reuse those nodes. Code folding, fibre evaluation and proof construction preserve DAG sharing with call-local tables. Those tables grant no admission capability or conversion authority. Declaration admission includes native Empty, List codes and universe paths; no receipt admits element-relation, higher-field or function-identity programs or guarded list inhabitants.

**Choice.** One code fold produces relation combinators; a shared evaluator computes both modes, while only identity carries reflexivity and transport. Separate per-mode recursions would duplicate the former clauses. Native identity syntax would couple the rule language to persistent declarations before its dependent substitution laws are checked. **Reversal.** Integrating element identity requires native syntax, scoped dependent motives and checked reduction/substitution laws; accepting Abstract requires its missing interface, not a default relation.

**Mutation scope.** The witnesses in `identity_recursion::tests` and `identity_recursion::function::tests` distinguish wrong sum branches, dropped product coordinates, negative equality on neutrals, forged identity evidence, incorrect universe classifiers, seal inspection and malformed Empty elimination. Function-specific boundaries include omitted or extra coverage, reused component dialogues, forged returned values, unchecked argument relations, bridge transport and application-motive action. No mutation score is claimed.

## Guarded higher fields

The `higher_field` module computes `Rel₂(p, q)` by quoting the native fibre of two checked parallel identities and applying the same identity-mode code fold to their evidence. No relation clause is duplicated. Neutral fibres retain the existing named refusal; the field adds no equality decision on unknown indices.

A `Codata` program is a flat graph of `Guard` and `Redirect` instructions. Each guard checks an inhabitant of the current higher fibre; its tail requests identity of that inhabitant with itself. The same API also observes any supplied pair of parallel native cells. A guarded cycle represents arbitrarily many requested diagonal layers without materializing an infinite structure. A cycle of redirects returns `NonProductive`. Success is a `Prefix` at exactly the requested positive `Depth`, not a verdict about an unobserved tail.

`ObservationBudget` gives each observation an instruction allowance from `ReplayBudget`. Every redirect and guard consumes one unit; reaching the allowance before the requested depth returns `DepthBound`. Zero depth returns `ZeroDepth`. CBPV dialogues and path formation retain their independent replay ceilings. Native relation checking remains a terminating structural walk, not part of the instruction count. These bounds state replay scope, not a global cost theorem.

`symmetry` checks that the source diagonal and inverse fibres have the same native type. It reindexes diagonal evidence into the path fibre, observes its higher identity with the supplied path evidence, and transports the diagonal in that fibre to produce the inverse. It then checks all four square faces and observes identity between the two boundary composites. Both Bool injections compute with distinct neutral Unit payloads and canonical evidence. A neutral proof-index action retains the existing transport boundary as `NeutralTransport`; this is not general dependent elimination.

`unfold` consumes two native `Value::PathEquiv` introductions, checks each through the ordinary closed-value checker and exposes the identity record:

| Field | Observation |
| ----- | ----------- |
| Forward | Replay both translators at the input; check identity of their returned values and its higher diagonal. |
| Backward | The same observation in the reverse direction. |
| Source coherence | Replay both backward-after-forward composites to the input; observe identity between their reflected diagonal witnesses. |
| Target coherence | The corresponding forward-after-backward coherence. |

The negation and case-inlined triple-negation certificates satisfy all four fields at both Bool constructors, while native structural conversion reports `Distinct`. This is **replay-equivalence as identity, never in conversion**. The record is an identity type’s observation interface: each point consumes supplied evidence; observing Base samples would not prove a universal field. Reflexivity and product introductions retain their native path operations; record unfolding requires `PathEquiv`.

`Identity::native_evidence` projects native fibre inhabitants only. Quantified function evidence returns `HigherEvaluationRequired`, preserving the distinction between a higher-evaluation program and a native value; suspended diagonals retain `NeutralFiber`. Function consumers borrow identities and replay their raw evidence.

**Choice.** A first-order cyclic program makes guards and back edges inspectable and bounds each replay. Eager towers cannot represent infinite higher data; closures hide productivity obligations and allocate opaque continuations. The graph stores no checking verdict and adds no dependency or wire tag. **Reversal.** A native higher identity language would replace the auxiliary representation only with checked substitution, reduction and persistence rules. Each observed native fibre must be representable at the admitted stratum; J and a general dependent eliminator are not provided.

**Mutation scope.** The higher-field module and its native-evidence projection: removed guards, uncharged redirects, early depth success, forged fibre evidence, dropped product coordinates, wrong square boundaries, substituted translator outputs and omitted round-trip coherence. The witnesses target these boundaries without claiming a mutation campaign or metatheorem about infinite coherence.

## Recursive code observations

`ValueType::List(A)` is the finite, strictly positive code `μX. Unit + A × X`, at A’s universe level. Wire tag `0x50` carries its element type; `0x51` is reserved and refused. Structural code conversion compares the finite element code, without unfolding a recursive value. The code survives ordinary encoding, decoding, substitution and content-support traversal.

`identity_recursion::recursive` reuses `higher_field::Codata`. Each `Guard` exposes `inl ()` for Nil or `inr head` for Cons, with the Cons recursive coordinate in its tail edge. `Redirect` exposes no constructor. A Nil never reads its tail. `Relation::observe_lists` uses the same fold’s element relation, returns Unit only after both finite spines end, and returns Empty at the first differing head or constructor. Neither verdict validates an unobserved tail.

One shared `ReplayBudget` counts both graphs’ Guard and Redirect visits. A constructor pair costs two instructions; a list of length n compared through Nil costs 2(n + 1). Returned progress includes the terminal or distinguishing constructor. Element checking and each CBPV replay retain separate finite bounds; this is an observation count, not a global work theorem.

`ListEquivalence::form` checks an element equivalence and lifts its forward and inverse maps constructorwise. Nil is fixed; Cons maps its head and delays the tail. Finite-list round trips follow by spine induction from the checked element round trips. Transport rechecks that raw certificate, replays each claimed head output, preserves constructors and consumes precisely one dialogue per Cons. Bool negation computes on empty, singleton and three-element lists through the same rule.

`Refusal` retains the existing `NonProductive` verdict for constructor-free cycles and `DepthBound` for exhausted observations, together with completed depth and visited instructions. A productive infinite spine still returns `DepthBound`: productivity does not establish a finite equality decision. No new uncertified-stratum error or recursive conversion rule is introduced.

**Choice.** A native finite List code plus borrowed guarded inhabitants keeps code identity decidable and list observations incremental. Eager unfolding cannot retain an unobserved tail; recursive Rust data would compromise bounded stack use. **Reversal.** General strictly positive descriptions or persisted inhabitants require their own constructor, substitution and persistence rules; this surface supports the List fixed point and first-order element observations.

**Mutation scope.** Recursive witnesses distinguish swapped constructor branches, dropped heads, eager tail reads, missing instruction charges, false productivity, truncated coverage, corrupt transport dialogues and finite-depth success on infinite input. No mutation campaign or infinite-coherence theorem is claimed.

## Sharing and persistence

The crate holds no interning table of decoded values that conversion consults, no content-keyed memo on the conversion path, and no persistence. The sharing a decode hands over is the sharing the checker sees, and identity equality is conversion's only sharing-aware step. The kernel's own type conversion performs no search, so it records no conversion trace; the replay is where the kernel reads one.

The one place the kernel creates sharing is the rewrite memo, and it is fenced: it shares only among nodes the kernel itself minted past the admission watermark, and nothing decides on that sharing, because conversion's identity fast path is positive-only.

## Mutation findings

An inert mutation identifies what the design does not depend on.

- **The plane component of the deciding comparison is inert.** Deleting `self.plane == other.plane` from `NodeSupport::agreement` leaves the suite green: the encoding's first byte is the goal's direction tag, and the two type-formation directions draw from a disjoint part of that alphabet, so the encodings already separate the planes. The plane field is load-bearing for accounting, not for agreement; the check stays as defence against a direction tag that does not separate.
- **A trap pair has to exhibit its ambiguity inside one framed unit.** The length-prefix pair is stated over a numeric literal, which carries two text payloads in one record, so `1.23` and `12.3` concatenate to the same digits and dropping the length prefix is killed. Over two text literals the pair would be inert, because the record framing separates two records whatever their payloads do.
- **The digest is killed only by its own witnesses.** Collapsing every digest to one constant changes no verdict and no count — it costs a linear bucket scan — and is killed by the digest's unit witnesses rather than by any verdict test, the positive-fast-path design seen from the other side.
- **The conversion discharged set times out rather than dying.** Removing it leaves the suite unable to finish: the claim it carries is intensional and exponential, and a timeout stays indeterminate rather than counting as a kill. A surviving mutant and an unfinished one call for opposite work.

Removing the outstanding-staged-content guard from `add_decl` is killed by the witness that the later staging’s root still resolves after refusal. An anonymous `const` assertion separately checks every assigned node tag against the private dangling sentinel `0xFF`; it checks tag values rather than the length of the sparse table. A named unused constant would not establish that build-time guard.

## Specification attributes

The `# Specification` prose is the statement of record. A combined `#[spec(...)]` attribute mirrors expressible requirements and postconditions, and each predicate appears verbatim in its prose clause. Both admission choke points carry one:

- `Environment::add_decl`: on success exactly one entry is appended and the admission floor ends at the arena's own watermark, the machine form of "the checker's intermediates were truncated rather than committed". Whether the declaration is well-typed is what the body decides and is not restated.
- `Environment::add_decl_unchecked`: the same, plus the entry carrying `Admission::Unchecked` and the arena watermark unmoved, so the warned bypass cannot quietly grow or shrink the arena.
- `check_sealing_provenance`: the ascending half, stated as a sortedness test rather than through the body's own previous-index loop. The occurrence half would re-derive the projected-atom set and double a walk over the declared type.
- `StagedMarks::resolve` and `ContentEncoding::put_word`: exactly one mark gone when one was held, and the varint terminator.

Further attributes check the level-scope boundary, the universe-order precondition, sealed-atom universe lookup, conversion mode-switch results, outstanding-mark counts, rewrite counts, and both type-witness projections. Conversion and witness postconditions repeat their named query only in the enforcing lane; no capture allocates or runs extra work in the ordinary lane.

Each prose-only block names its boundary in `- provides:`: a cross-input law, arena provenance, a lifecycle transition, or a semantic graph judgement needing an independent traversal. The two const register projections keep their API without attributes, because the attribute's expansion calls a non-const evaluator (`E0015`). Runtime checks do not establish the adequacy hypotheses; the witnesses do.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
