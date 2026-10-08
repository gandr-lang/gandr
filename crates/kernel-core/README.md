# gandr-kernel-core

The certified kernel's judgements: the defunctionalized checking machine, type formation, conversion, the admission choke point, and the check memo wired as the default path on both machines.

Representation, the sharing format and the decode budgets belong to `gandr-kernel-term` below this crate; the universe algebra to `gandr-kernel-strata`; the memo's storage to `gandr-kernel-check-memo`. What lives here is what re-derives an obligation.

## Provision

- **The checking machine.** Bidirectional, annotation-free, and defunctionalized over a goal register, a produced register, a heap frame stack and an explicit typing-context stack. Its arm-by-arm correspondence table is the module doc of `check`, and it is the trusted-base audit artifact: a reviewer walks it to confirm the machine _is_ the judgement rather than an approximation of it.
- **Type formation.** A second iterative walk that computes a type's universe level, gating lift strictness, level scope, and a sealed atom's kind.
- **Conversion.** Structural comparison of two types, descending into the terms they carry, with an id-equality fast path above it. The fast path is **positive only**: equal ids discharge a pair, unequal ids decide nothing and fall through to the structural walk. That asymmetry is what makes it sound while taking no table into the trusted base. No reduction fires: two codes convert when they are structurally equal, which is sound and incomplete, and closing the gap is the convertibility machine's job.
- **Admission.** One checked choke point, one warned bypass, and a per- declaration audit of what a declaration transitively rests on. The arena is truncated on both verdicts — to content-end on success, to the declaration's content-start on rejection, clamped at the admission floor — and a declaration with a **later staging still outstanding above it** is refused rather than rolled back, because a contiguous truncation cannot spare a disjoint region.
- **The memo, on by default, on both machines.** Admitting one declaration runs two iterative machines over the shared graph, and both consult the memo.

## The memo's six binding conditions

The seam crate ports verbatim precisely because it names no term type; everything that makes a memo _sound_ is a consumer obligation, and this crate is the consumer.

| condition | discharged by |
| --------- | ------------- |
| static dispatch on a null-object seam that compiles away | `check_declaration_with_memo` is generic over `CheckMemo`; every interaction sits behind `matches!(M::ACTIVITY, Active)` |
| the public admission entry cannot reach the opt-in entry | `Environment::add_decl` takes no memo and builds its own; the memo-taking entry returns a verdict and never a `CheckedId` |
| a lifetime of one check call | `check_declaration` builds a memo and a session and drops both; a support is meaningful only against its own session |
| the content-only key | `(direction, obligation content, expected content, telescope content)` — no arena id, no allocation order |
| storage and policy outside the kernel crate | the seam crate owns the table, its ordering and its eviction; this crate holds a type parameter |
| no authority and no persistence in a hit | a hit claims only that this process already computed this answer for this support |

**Why the lifetime rule survives the content key.** Under an arena-identity key the one-call lifetime was a _consequence_: ids dangle once the choke point truncates. A content key dissolves that reason, so the rule rests on the two-wall discipline directly — a hit claims only its own history, and no kernel-checked support discipline exists. A second reason survives independently: an _outcome_ still carries arena ids even though the key does not.

## The key derivation

Content is named by a content id, assigned by interning each node's one-level record — its tag, its inline payload, and its children's already-assigned ids — bottom-up and exactly. No hash decides an id. The digest above it is a **positive fast path only**: different digests prove disagreement, equal digests hand off to byte equality of the canonical support encodings, and a collision costs one comparison and degrades to a miss.

Injectivity is carried by four trap pairs riding on the record encoder rather than by randomized testing, because key collision is the one obligation a randomized differential cannot probe: two field orders, two families sharing a payload, signed zeroes, and the length-prefix ambiguity pair.

Each distinct node is encoded once per session, so deriving every key of one check costs one pass over the distinct nodes — linear rather than quadratic even on a chain-deep term a decoder built from bytes.

## Measured acceptance

The self-similar composite is `t_0 = ()`, `t_{k+1} = (t_k, t_k)` against `T_0 = Unit`, `T_{k+1} = T_k x T_k`. The law is asserted as a closed form at three depths, decomposed per plane, rather than sampled.

| depth | memoless total | memoless term | memoless type | memoized total | memoized term | memoized type | collapse |
| ----- | -------------- | ------------- | ------------- | -------------- | ------------- | ------------- | -------- |
| 8 | 1,278 | 767 | 511 | 19 | 10 | 9 | 67x |
| 12 | 20,478 | 12,287 | 8,191 | 27 | 14 | 13 | 758x |
| 16 | 327,678 | 196,607 | 131,071 | 35 | 18 | 17 | 9,362x |
| 28 | 1,342,177,278 | — | — | 59 | 30 | 29 | 22.7M x |

Memoless is `5 * 2^d - 2` in total, `3 * 2^d - 1` body checks against `2^(d+1) - 1` type formations. Memoized is `2d + 3`, `d + 2` term supports against `d + 1` type supports. The depth-28 row is the capability, and it is measured at the public choke point: a definition whose tree expansion is 1,342,177,278 goals admits **checked** through `Environment::add_decl`, with no bypass. Its memoized columns are asserted through the opt-in entry on the same shape; its memoless columns are the closed form's value and are never run.

**Anti-vacuity, on both sides.** The occurrence count is pinned by the memoless term-plane law, so the workload cannot stop being shared unnoticed. The memo's own entry count is compared against the census from the other direction, per plane and in total. And a separate case pins that the shared composite and its fully unshared spelling cost the **memoless** checker identically — which is the statement that sharing bought checking nothing before the memo existed.

**Edit locality: `d + 1` node checks per depth-`d` edit,** measured within one check call. Both spellings are checked in one pass, because warming a memo on the original and reusing it across calls would measure exactly the unsound thing the lifetime rule forbids. Measured extra term-plane expansions: 9 at depth 8, 13 at depth 12, 17 at depth 16. The type plane adds nothing, because the edit changes no type. The `d + 1` rather than `d + 2` is the content key: the edited leaf's freshly minted payload collapses with the original's.

**Adversarial depth.** A 20,000-link `thunk`-over-`return` chain checks totally inside a 256 KiB stack, at both memo instantiations, costing 40,002 term-plane expansions — asserted, so the case cannot degenerate into a shallow term and keep passing.

## Teeth

Permanent suite members, in both directions and on both planes, each asserting its exercised-path count through the expansion census:

- a poisoned term entry turns a refusal into an acceptance (served once);
- an entry differing only in its binder component is **not** served (served zero times), with a positive control under the matching telescope that does change the verdict, so the case measures the binder component rather than an inert poison;
- a poisoned type-formation entry turns an admission into a universe-violation refusal (served once, on the type plane);
- a term-shaped answer in a type-formation support is declined and recomputed at exactly the cost of having had no entry, and the mirror case on the term plane.

## Staging order, and what admission refuses

A staged declaration outlives its builder's borrow, so staging order need not be admission order. That divergence has two shapes and only one is absorbable.

**Content-start below already-admitted content** is absorbed by the admission floor: a rejection clamps its rollback into `[floor, content-end]`, so it never deletes committed content and never leaves an intermediate behind, retaining the rejected declaration's own nodes as unreachable orphans instead. Retaining garbage is the failure that trades for deleting evidence.

**Content-start below _outstanding_ content is refused.** Stage one declaration, stage a second, then offer the first: the second's nodes sit above the first's content-start while its `StagedDeclaration` is live, the floor lies below both, and a contiguous truncation cannot spare a disjoint region. Performing the rollback would hand the producer dangling roots — or, worse, free indices a later staging re-mints, so a subsequent admission would check _other_ content and admit a different declaration under that name. The environment therefore tracks the content-start mark of every staged, unresolved declaration and answers `KernelError::OutstandingStagedContent` naming how many sit above. A silent index retarget is the one outcome the floor's evidence-preservation rule exists to rule out, so the refusal is the fail-closed posture the rest of the kernel takes.

A mark is resolved by admitting, bypassing, or `Environment::abandon`; abandoning a staging session before it finishes resolves its mark too. `abandon` truncates when nothing outstanding sits above the mark and retains the region as an orphan otherwise, which is the same clamp a rejection takes. "Above" is componentwise rather than lexicographic, because truncation is per family.

## Conversion is sharing-aware

`converge` carries a per-call set of discharged pairs. Without it two roots that share a subgraph re-walk every shared pair once per occurrence, so the work is the _expansion_ of the compared graphs rather than their size — exponential in sharing depth on a term a decoder handed over. A pair discharged once stays discharged: at this subset a type pair's verdict is a function of the two nodes alone, and any pair that fails returns immediately, so nothing is recorded as discharged while its own subtree is undecided. The set holds only pairs, creates no sharing, is consulted for nothing but skipping a repeat inside one comparison, and dies with the call.

## Findings from inert mutations

Recorded rather than deleted, because an inert mutation identifies what the design does not depend on.

- **The plane component of the deciding comparison is inert.** Deleting `self.plane == other.plane` from `NodeSupport::agreement` leaves the whole suite green: the encoding's first byte is the goal's direction tag, and the two type-formation directions draw from a disjoint part of that alphabet, so the encodings already separate the planes. The plane field is load-bearing for _accounting_, not for agreement. The redundant check is kept as defence against a future direction tag that does not separate.
- **A trap pair that framing already separated.** Dropping the length prefix from a text payload was initially inert, because two literals sit in two records and the record framing separates them whatever their payloads do. The pair was restated over a numeric literal, which carries two text payloads in **one** record, so `1.23` and `12.3` concatenate to the same digits — and the mutation is now killed. The finding is about the shape of a trap pair: the ambiguity has to be exhibited inside the unit the encoder frames.
- **The digest is killed only by its own witnesses.** Collapsing every digest to one constant changes no verdict and no count — it costs a linear bucket scan — and is killed by the digest's L3 unit witnesses rather than by any verdict test. That is the positive-fast-path-only design seen from the other side.
- **The conversion discharged set is `timed_out`, not killed.** Removing it leaves the suite unable to finish rather than failing: the claim it carries is intensional and exponential, and a timeout stays indeterminate rather than collapsing into a kill. Recorded as what it is, because a surviving mutant and an unfinished one call for opposite work.

Two mechanisms added under review are pinned as genuine kills: removing the outstanding-staged-content guard from `add_decl` is **killed** by the witness that the later staging's root still resolves after the refusal, and shortening the node-tag block below the dangling sentinel is a **build failure**, since the reservation is an anonymous `const` assertion rather than a named one — a named unused constant is never evaluated, so `const _NAME: () = assert!(..)` would be a guard that does not guard.

## The contract attributes

The `# Specification` prose stays the statement of record. A combined `#[spec(...)]` attribute mirrors expressible requirements and postconditions; each new predicate appears verbatim in its prose clause. Fourteen items carry attributes, including both admission choke points:

- `Environment::add_decl` — on success exactly one entry is appended and the admission floor ends at the arena's own watermark, which is the machine form of "the checker's intermediates were truncated rather than committed". Whether the declaration is _well-typed_ is what the body decides and is not restated.
- `Environment::add_decl_unchecked` — the same, plus the entry carrying `Admission::Unchecked` and the arena watermark unmoved, so the one warned bypass cannot quietly grow or shrink the arena.
- `check_sealing_provenance` — the ascending half, stated as a sortedness test rather than through the body's own previous-index loop. The occurrence half would mean re-deriving the projected-atom set and doubling a walk over the declared type.
- `StagedMarks::resolve` and `ContentEncoding::put_word` — exactly one mark gone when one was held, and the varint terminator.

The other attributes check the level-scope boundary, the universe-order precondition, sealed-atom universe lookup, conversion mode-switch results, outstanding-mark counts, rewrite counts, and both type-witness projections. Conversion and witness postconditions repeat their named query only in the enforcing lane; no new capture allocates or runs extra work in the ordinary lane.

Each remaining prose-only block names its boundary in `provides`: cross-input laws, historical provenance, lifecycle transitions, or semantic graph judgements needing independent traversals. These are residual obligations, not empty attributes or weakened predicates. The two const register projections preserve their API without attributes because the pinned expansion calls a non-const evaluator (`E0015`). Existing adequacy hypotheses and witnesses remain unchanged; runtime checks do not establish their claims.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## What this crate refuses to hold

No interning table of _decoded_ values that conversion consults, no content-keyed memo on the conversion path, and no persistence. The sharing a decode hands over is the sharing the checker sees, and identity equality is conversion's only sharing-aware step. The conversion trace's static sink has no consumer here — conversion at this type vocabulary performs no search, so it makes no decision worth recording — and it acquires one when the convertibility machine lands.

The one place the kernel _creates_ sharing is the rewrite memo, and it is fenced rather than excepted: it shares only among nodes the kernel itself minted past the admission watermark, and nothing decides on that sharing, because conversion's identity fast path is positive-only.

## The dependent arrow, the two rewrites, and the deferred codes

The dependent arrow forms at the join of its children like the non-dependent one, and a lambda checks against it through the domain slot its codomain is already written against. What makes it dependent is the universe-decoding former: a type read off a **code**, a value whose type is a universe, and the only former whose child crosses from the type language into the term language.

**The carried level is what keeps the two machines two machines.** The former names the universe it is read out of, so type formation is a lookup rather than an inference, and the obligation it cannot discharge — that the code inhabits that universe — is _recorded_ rather than pursued. The driver drains the record through the checking machine, and a drained check that owes further codes appends to the same worklist. Neither walk calls the other, so the recursion ban is met by the architecture rather than by a depth budget. The drain carries a ceiling derived from the format's subterm-table cap, because a drained check can form a synthesized type and owe more codes, so the loop's bound is not the artifact's own size.

**The two de Bruijn rewrites its rules stand on are here as machines.** Shifting raises every free index at or above a cutoff; substitution replaces the innermost binder's variable and lowers everything outside it. Both are loops over an explicit task stack and an explicit results stack, so they are total on a term a decoder built from bytes, and each is memoized at its own instantiation of the check-memo seam so a shared subterm is rewritten once rather than once per occurrence. Carrying a replacement under a crossed binder is a shift, and the engine schedules it as a task on the same stack rather than calling itself.

Two sites in the checker consume them: a variable synthesis raises its context slot past the binders between the slot and the use site, and an application at a dependent head instantiates the codomain at its argument. Those two faces — shifting a value type, instantiating a computation type — are the crate's public rewrite surface; the machines' other four family faces stay crate-visible until a production caller wants them, and the compiler says so rather than a comment. A type carrying no code rewrites to itself and the walk hands back the node it was given, so the common case costs nothing and the sharing a decode preserved survives.

The audit graph follows codes. A declaration's declared type reaches another declaration two ways — a sealed atom names one directly, and a code names one through the term language — and the trust report is a false negative if it follows only the first. The sealing-provenance set deliberately does **not** follow codes: it asks which sealed atoms a projection rebound, and widening it would make the gate more permissive on the one surface whose job is to be falsifiable.

## Plan mapping

Implements the `kernel-core` milestone of the ratified normalizer and elaborator plan, together with the `pi` milestone's dependent arrow, its two de Bruijn rewrites, and the type former indexed by a value term.

| plan module | anchor | what this crate carries |
| ----------- | ------ | ----------------------- |
| kernel | `checking-machine` | the defunctionalized machine and its correspondence table |
| kernel | `one-context` | one flat, de Bruijn, id-addressed, name-free context; a single-valued error face |
| kernel | `arena-watermark` | constructor-only minting, the admission watermark, the anti-commitments |
| architecture | `pipeline-split` | pipeline steps 1 and 3 as the kept fast paths: identity equality, then structure |
| incremental | `check-memo-vocab` | the seam consumed at two instantiations, with the memoless path differentialed |
| incremental | `support-is-soundness` | the content-only key, the loose-depth pass, the digest contract, the trap pairs |
| incremental | `recorded-numbers` | the collapse law and the edit-locality figure, asserted as closed forms |
| incremental | `two-machines-one-memo` | one memo, two machines, per-plane accounting |

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

The content key is a settled commitment carrying an unmeasured trade, recorded as `norm-decision-content-memo-key` on the plan's question surface: its cost is now measured in shape — one pass over the distinct nodes of a check — but what it buys over an identity key on a real corpus still has no number attached, and a measurement showing the cost dominating the reuse payoff is what re-keys it.

The conversion discharged set is a bound on the conversion path and therefore outside the four ratified amplification budgets, which are a design-page matter. It is taken here because the surface it guards is public — a direct arena caller is not behind the decoder's expanded-work gate — and because it is a strict improvement with no extensional face. It is recorded for owner ratification rather than assumed.
