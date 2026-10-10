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
- [Sharing and persistence](#sharing-and-persistence)
- [Mutation findings](#mutation-findings)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `Environment` admits declarations through one checked choke point, `add_decl`, and one warned bypass, `add_decl_unchecked`; `audit` reports what an admitted declaration transitively rests on. Beneath the choke point sit a bidirectional checking machine, a type-formation walk that computes a type's universe level, and structural conversion. Beside it, `replay` rechecks a term-conversion verdict an untrusted engine reached, decision by decision, from the trace that engine recorded. Representation, the sharing format and the decode budgets belong to `gandr-kernel-term`, the universe algebra to `gandr-kernel-strata`, the memo's storage to `gandr-kernel-check-memo`, and the decision vocabulary to `gandr-kernel-conversion-trace`; this crate is what re-derives an obligation.

**Why.** The kernel grants a producer no credence: every declaration is re-checked before admission, including one a decoder built from untrusted bytes. Such a term can be arbitrarily deep and heavily shared, so the checker must be total on adversarial depth and must not pay for a shared subterm once per occurrence.

**How.** The checker is a defunctionalized machine over a goal register, a produced register, a heap frame stack and an explicit typing-context stack, never mutually recursive methods bounded by a depth budget, so it is total on depth. The arm-by-arm correspondence table in the `check` module docs is the trusted-base audit artifact: a reviewer walks it to confirm the machine is the judgement. Conversion is structural comparison with a positive-only id-equality fast path: equal readable ids discharge a pair; unreadable roots refuse, and unequal ids require the structural walk. Both machines consult a check memo keyed by content, so a shared subterm is checked once per distinct support, and the memo lives for one check call. Admission truncates the arena on both verdicts, clamped at the admission floor so a rollback never deletes committed content.

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

Conversion carries a per-call set of expanded pairs. Without it, shared subgraphs are re-walked once per occurrence, making work exponential in sharing depth. A pair enters the set before its children are compared; its first expansion leaves every required child on the worklist. Repeated pairs therefore skip expansion without dropping those obligations. Any failing child refuses immediately, and conversion requires an empty worklist. The set holds only pairs, creates no sharing, and dies with the call.

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

## Sharing and persistence

The crate holds no interning table of decoded values that conversion consults, no content-keyed memo on the conversion path, and no persistence. The sharing a decode hands over is the sharing the checker sees, and identity equality is conversion's only sharing-aware step. The kernel's own type conversion performs no search, so it records no conversion trace; the replay is where the kernel reads one.

The one place the kernel creates sharing is the rewrite memo, and it is fenced: it shares only among nodes the kernel itself minted past the admission watermark, and nothing decides on that sharing, because conversion's identity fast path is positive-only.

## Mutation findings

An inert mutation identifies what the design does not depend on.

- **The plane component of the deciding comparison is inert.** Deleting `self.plane == other.plane` from `NodeSupport::agreement` leaves the suite green: the encoding's first byte is the goal's direction tag, and the two type-formation directions draw from a disjoint part of that alphabet, so the encodings already separate the planes. The plane field is load-bearing for accounting, not for agreement; the check stays as defence against a direction tag that does not separate.
- **A trap pair has to exhibit its ambiguity inside one framed unit.** The length-prefix pair is stated over a numeric literal, which carries two text payloads in one record, so `1.23` and `12.3` concatenate to the same digits and dropping the length prefix is killed. Over two text literals the pair would be inert, because the record framing separates two records whatever their payloads do.
- **The digest is killed only by its own witnesses.** Collapsing every digest to one constant changes no verdict and no count — it costs a linear bucket scan — and is killed by the digest's unit witnesses rather than by any verdict test, the positive-fast-path design seen from the other side.
- **The conversion discharged set times out rather than dying.** Removing it leaves the suite unable to finish: the claim it carries is intensional and exponential, and a timeout stays indeterminate rather than counting as a kill. A surviving mutant and an unfinished one call for opposite work.

Two guards are pinned as kills. Removing the outstanding-staged-content guard from `add_decl` is killed by the witness that the later staging's root still resolves after the refusal. Shortening the node-tag block below the dangling sentinel is a build failure, because the reservation is an anonymous `const` assertion: a named unused constant is never evaluated, so `const _NAME: () = assert!(..)` would not guard.

## Specification attributes

The `# Specification` prose is the statement of record. A combined `#[spec(...)]` attribute mirrors expressible requirements and postconditions, and each predicate appears verbatim in its prose clause. Both admission choke points carry one:

- `Environment::add_decl`: on success exactly one entry is appended and the admission floor ends at the arena's own watermark, the machine form of "the checker's intermediates were truncated rather than committed". Whether the declaration is well-typed is what the body decides and is not restated.
- `Environment::add_decl_unchecked`: the same, plus the entry carrying `Admission::Unchecked` and the arena watermark unmoved, so the warned bypass cannot quietly grow or shrink the arena.
- `check_sealing_provenance`: the ascending half, stated as a sortedness test rather than through the body's own previous-index loop. The occurrence half would re-derive the projected-atom set and double a walk over the declared type.
- `StagedMarks::resolve` and `ContentEncoding::put_word`: exactly one mark gone when one was held, and the varint terminator.

Further attributes check level-scope precedence, consistency evidence, universe-refusal subjects and strictness, sealed-atom universe lookup, readable conversion identities and head separation, conversion mode-switch results, saturating census transitions, outstanding-mark counts, rewrite counts, and both type-witness projections. Mode-switch and witness postconditions repeat their named query only in the enforcing lane; no capture allocates or runs extra work in the ordinary lane.

Each prose-only block names its boundary in `- provides:`: a cross-input law, arena provenance, a lifecycle transition, or a semantic graph judgement needing an independent traversal. The two const register projections keep their API without attributes, because the attribute's expansion calls a non-const evaluator (`E0015`). Runtime checks do not establish the adequacy hypotheses; the witnesses do.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
