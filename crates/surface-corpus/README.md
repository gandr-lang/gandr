# gandr-surface-corpus

The expectation language over a lowered module and its verdicts — the eight claim schemas, the strict and fixture corpus roots, the comparison that settles each name, and the report a corpus runner reads its counts from — and the language's corpus itself, the strict root under `strict/` and the fixture root at the repository's top under `corpus/`.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Writing to the corpus](#writing-to-the-corpus)
- [Comments](#comments)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `settle` takes a `CorpusRoot`, the `CoreArena` a module was lowered into, the `LoweredModule` and the checker's `ModuleReport` for it, and answers a `SettleReport`: per declared name, what its attributes state, what it produced and what its verdict owes, plus the module's ledger size. `SettleReport::tally` sums a run into a `Tally` a driver absorbs, gates on and prints.

**Why.** A corpus that only says pass or fail cannot tell a run that owes nothing from one that signed for a hole, and a corpus whose sources describe their own expected failures can describe a regression as expected. The expectation language here makes both visible: the strict root admits only `checks` and its refinements, every declaration states a verdict whether it writes one or not, and every report carries the ledger size.

**How.** `settle` reads each declared name's attributes off the lowering's side table and walks the declarations in admission order beside the checker's verdicts. A stated run goes through the caller's `Runner`, a stated normal form through `LoweredModule::normal_form`. One equality decides each declaration, and the tally counts it once.

## Provided features

- `CorpusRoot` and `CorpusRoot::admit`: the two roots and the strict root's refusal of `owes` and `refuses`.
- `ExpectationSchema` and `expectation_schema::Absent`: the eight schemas, matched by the registry's names.
- `Runner`, `RunSpelling` and `ran::Absent`: the run or web a `runs` or `decomposes` outcome is compared against, asked of the caller, accepted or refused, the line a `normalizes` outcome is compared against, and the items a `reads` names; `TracedRun` and `Channel`: a run and the web each channel it forked played; `stating_reads` and `reads_spelled`: who states a `reads`, and its spelling.
- `normalized_call`, `normalized_call::Absent` and `NORMAL_FORM_ARROW`: the call a `normalizes` line reads, why a line reads none, and what separates a call from its normal form.
- `Stated`, `Outcome`, `ExpectationFault`, `Membership` and `Expectations`: what a declaration states, and why an expectation states nothing; `expected`: one lowered declaration's expectations, read without settling.
- `RefusalName`, `RefusalSpelling`, `refusal_name::Absent`, `Refusal` and `CorpusRefusal`: the closed refusal vocabulary and producer refusal views; `RefusalName::closed`: every name no form qualifies.
- `settle`, `SettleFault`, `Produced`, `produced_refusal::Absent`, `DeclarationReport`, `Settlement` and `Surviving`: the settle comparison; `settle_after`: a module settled after its leading declarations' reports.
- `SettleReport`, `Tally`, `SettleCounts`, `ClassCounts` and `Seal`: the report and its counts.

## Expected features

- **One arena.** The caller supplies the arena the lowering minted the module into; `settle` states what its identifiers cannot establish.
- **The module's own verdicts.** The caller supplies the checker's report for exactly the declarations the lowering did not refuse, in admission order; `settle` refuses a missing, shifted or surplus one by position.
- **`alloc`.** The crate is `no_std` with `alloc`, and does no I/O, no file walking and no process exit.

## Examples

The crate-level doctest (`src/lib.rs`, § Example) is the example. `cargo nextest run -p gandr-surface-corpus` runs it with the crate's tests.

The control subjects take a case that is hard in other languages and write it as gandr does, the accepting programs under `fixture/model/<subject>/` and each misuse refused by name under `fixture/pathological/<subject>/`:

| Case | Subject | Compared with |
| ---- | ------- | ------------- |
| Async drop | `drop` | Rust's async-drop experiment and its `AsyncDrop` proposal; Swift's synchronous `deinit` (SE-0371); C++ destructors, which cannot await |
| Cancellation safety | `cancellation` | Rust's futures dropped at an `.await`; Kotlin's `NonCancellable` section |
| Completion-based I/O | `completion` | io_uring's submission and completion queues; Rust's owned-buffer completion APIs |
| Lifetime parameters | `regions` | Rust's lifetime parameters, `fn f<'a>(x: &'a T) -> &'a T`, and the free theorem of a function generic in `'a`: it cannot keep what it borrows |
| Move semantics | `moves` | C++'s moved-from objects and move constructors; Rust's `Copy` and move split, and `mem::forget` |
| Self-reference | `self-reference` | Rust's `Pin` for a future that borrows from itself (RFC 2349); C++ objects kept immobile by convention |
| Structured concurrency | `tasks` | Trio's nurseries; Rust's scoped threads (`std::thread::scope`) |

## Writing to the corpus

The corpus is a proof library and a test suite at once, and it grows by subject, not by accretion (#435). A change that adds a source or an item is held to these rules in review.

- **One subject, one directory, one base.** A subject (`identity`, `data`, `universe`, …) is one directory under `fixture/model/`; its shared declarations — `Circle`, `Int`, `Empty`, an isomorphism every file uses — live in one base source the others import (`import "./circle-base.gandr" ;`). No two sources of one subject declare a name: `gandr-surface-dispatcher`'s `no_subject_declares_a_name_twice` refuses that, and its documentation says what counts. A new directory only when no subject owns the claim.
- **One file, one claim.** A source states one theorem family or one feature, in the order the argument runs: definitions, then laws, then what refuses. Its head says what it proves and names the source it follows — a cubical file and line, a book section — and an item that follows a named lemma keeps that name in its comment. A lemma two files need is written in the file that owns it and imported, never restated; a new item goes to the file that owns its subject before a new file is opened.
- **Every item and block member carries its comment; every item its attribute.** `///` before the attribute block or the member, one of `checks`, `runs`, `normalizes`, `decomposes`, `reads`, `owes`, `refuses`, `runs` beside `refuses` for a refused program whose run is part of the claim, or `runs` beside one `traces` per channel for a run whose play is part of the claim. No claim means `checks`. A refused item sits beside the item it blocks, and its issue is a `- see: #n` line in the head's references (§ Comments); there is no `declined` fixture — a refusal the record admits is a defect to file and fix. A fix's regression is an item in the subject's file.
- **A refusal has a twin.** What a model source proves, `pathological/<subject>/` refuses by name, one refusal per item, the same subject directory on both sides.
- **A law sits beside what it governs.** A definition with an algebraic law — a unit, associativity, a functor's composition — states it as a `rule` of its own `data` or `theory` block, oriented by the order or by a written `==>`, so the coincidence check certifies it with the block's other rules, and a `normalizes` row fires it (`model/data/map-laws.gandr`, `model/identity/group-laws.gandr`). A law is never adjoined as an axiom: one the check cannot certify yet is refused by name in the subject's twin, naming the issue that admits it — a rule over a `def` (#525), a law that joins only through a cell completion derives (#338).
- **Size follows the sweeps.** A source stays within the per-source bounds the sweeps enforce; each sweep's ceiling states how it measures a source. Split by claim, never by count.
- **Names say the claim.** Files are kebab-case by subject and claim (`circle-group`, not `circle2`); items are the language's camelCase; a name that coincides with cubical's or the book's is kept.
- **Sugared, but where the spelling is the claim.** A corpus source is written in the sugared form `gandr fmt --form=sugared` writes: `A => B` for `+U (A -> -F B)`, `A * B` for `#{A, B}`, `def x : T = e ;` for a pair. A source whose claim is a former's own shape declares `@[ form(explicit) ]` at its head and keeps the explicit form: the arity sources (`surface/arity/` `product`, `sum`, `records`), the engine's fragment and classifier sources (`fragment/`, `classifier/`), the universe sources (`model/universe/` and `pathological/universe/`) and `model/identity/cong-thunk.gandr`, whose path lies in a thunk type. A refusal is sugared unless it is about the explicit form. `check:corpus` holds every source of both roots to this with `gandr fmt --check --form=sugared`.
- **The strict root is strict.** `strict/` admits only `checks` and its `runs`, `normalizes`, `decomposes`, `traces` and `reads` refinements.

The test suite follows the same shape: one witness per behaviour, in the crate that owns it, named as the sentence it proves; a corpus-wide property is a `sweeps` module test, and nothing else walks the corpus; a setup two crates share is one function called twice; a duplicate witness is deleted when found and the survivor named in the commit.

## Comments

Write as ASD-STE100 writes — short sentences, one topic a paragraph, active voice, present tense — with the technical vocabulary unrestricted. A source opens on four paragraphs: what it states (the first sentence at most twenty words), why, how, and `- see: <token> — <what it settles>` references, the only place a path, `#n` or page stands. An item comment is one sentence, a second allowed. No sentence runs past twenty-five words or joins another by a semicolon, and a passive is one of `is refused`, `is admitted`, `is replayed`, `is checked`, `is normalised`. The heads of `model/higher-cells/ua-by-hand.gandr` and `model/desc/atom-occurrence.gandr` are worked examples, and [`prose`](tests/comments/prose.rs) states the check (#2918).

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Specification and adequacy, inputs not a pipeline, references | [`src/lib.rs`](src/lib.rs) |
| One predicate: settled; lockstep with the checker | [`settle`](src/settle.rs) |
| Run outcomes, the strict root, one expectation per name | [`expectation`](src/expectation.rs) |
| Sealed and the ledger size | [`report`](src/report.rs) |
| The closed refusal vocabulary, native universe-path refusals | [`refusal`](src/refusal.rs) |
| Membership, the corpus directories, one walk, the pending set | [`root`](src/root.rs) |
| The kernel export suite | [`kernel_export`](src/kernel_export.rs) |
| A comment on every fixture item, the ledger ratchet | [`src/lib.rs`](src/lib.rs), [`comments`](tests/comments.rs) |

## References

- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the refusal `FootprintsOverlap`, classed a malformed source.
- `vault:01a178aa-6cd7-7ac2-a049-ee4124ad5576` — background: the layouts design (§ layouts-semantic-abi) — the clauses `BoundaryClause` names.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design (§ The declaration) — a port at a `Type[-]` sort.
- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: `NotATranslation`, a `via` riding no flow.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: a `via` naming no flow is a malformed source.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: a flow's code is demanded by a `via` alone.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
