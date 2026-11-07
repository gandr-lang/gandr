# gandr-surface-corpus

The expectation language over a lowered module and its verdicts — the nine claim schemas, the strict and fixture corpus roots, the comparison that settles each name, and the report a corpus runner reads its counts from — and the language's corpus itself, the strict root under `strict/` and the fixture root at the repository's top under `corpus/`.

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
- `ExpectationSchema` and `expectation_schema::Absent`: the nine schemas, matched by the registry's names.
- `Runner`, `RunSpelling` and `ran::Absent`: the run or web a `runs` or `decomposes` outcome is compared against, asked of the caller, accepted or refused, the line a `normalizes` outcome is compared against, and the items a `reads` names; `TracedRun` and `Channel`: a run and the web each channel it forked played; `stating_reads` and `reads_spelled`: who states a `reads`, and its spelling.
- `distributed`, `Bits` and `PastQuota`: the distribution a declaration's runs give in canonical form, the bits a path draws and the quota of 16, and why a path past the quota gives no distribution.
- `normalized_call`, `normalized_call::Absent` and `NORMAL_FORM_ARROW`: the call a `normalizes` line reads, why a line reads none, and what separates a call from its normal form.
- `Stated`, `Outcome`, `ExpectationFault`, `Membership` and `Expectations`: what a declaration states, and why an expectation states nothing; `expected`: one lowered declaration's expectations, read without settling.
- `RefusalName`, `RefusalSpelling`, `refusal_name::Absent`, `Refusal` and `CorpusRefusal`: the closed refusal vocabulary and producer refusal views; `RefusalName::closed`: every name no form qualifies.
- `settle`, `SettleFault`, `Produced`, `produced_refusal::Absent`, `DeclarationReport`, `Filler`, `Settlement` and `Surviving`: the settle comparison; `settle_after`: a module settled after its leading declarations' reports.
- `SettleReport`, `Tally`, `SettleCounts`, `ClassCounts` and `Seal`: the report and its counts.

## Expected features

- **One arena.** The caller supplies the arena the lowering minted the module into; `settle` states what its identifiers cannot establish.
- **The module's own verdicts.** The caller supplies the checker's report for exactly the declarations the lowering did not refuse, in admission order; `settle` refuses a missing, shifted or surplus one by position.
- **`alloc`.** The crate is `no_std` with `alloc`, and does no I/O, no file walking and no process exit.

## Examples

The crate-level doctest (`src/lib.rs`, § Example) is the example. `cargo nextest run -p gandr-surface-corpus` runs it with the crate's tests.

The control subjects write cases that are hard in other languages as gandr writes them. The table of the subjects, with the languages each one compares, is in [`root`](src/root.rs) § The corpus.

## Writing to the corpus

The corpus is a proof library and a test suite at once, and it grows by subject, not by accretion (#435). A change that adds a source or an item is held to these rules in review.

- **One subject, one directory, one base.** A subject (`identity`, `data`, `universe`, …) is one directory under `fixture/model/`; its shared declarations — `Circle`, `Int`, `Empty`, an isomorphism every file uses — live in one base source the others import (`import "./circle-base.gandr" ;`). No two sources of one subject declare a name: `gandr-surface-dispatcher`'s `no_subject_declares_a_name_twice` refuses that, and its documentation says what counts. A new directory only when no subject owns the claim.
- **One file, one claim.** A source states one theorem family or one feature, in the order the argument runs: definitions, then laws, then what refuses. Its head says what it proves and names the source it follows — a cubical file and line, a book section — and an item that follows a named lemma keeps that name in its comment. A lemma two files need is written in the file that owns it and imported, never restated; a new item goes to the file that owns its subject before a new file is opened.
- **Every item and block member carries its comment; every item its attribute.** `///` before the attribute block or the member, one of `checks`, `runs`, `normalizes`, `decomposes`, `reads`, `distributes`, `owes`, `refuses`, `runs` beside `refuses` for a refused program whose run is part of the claim, or `runs` beside one `traces` per channel for a run whose play is part of the claim. No claim means `checks`. A refused item sits beside the item it blocks, and its issue is a `- see: #n` line in the head's references (§ Comments); there is no `declined` fixture — a refusal the record admits is a defect to file and fix. A fix's regression is an item in the subject's file.
- **A refusal has a twin.** What a model source proves, `pathological/<subject>/` refuses by name, one refusal per item, the same subject directory on both sides.
- **A law sits beside what it governs.** A definition with an algebraic law — a unit, associativity, a functor's composition — states it as a `rule` of its own `data` or `theory` block, oriented by the order or by a written `==>`, so the coincidence check certifies it with the block's other rules, and a `normalizes` row fires it (`model/data/map-laws.gandr`, `model/identity/group-laws.gandr`). A law is never adjoined as an axiom: one the check cannot certify yet is refused by name in the subject's twin, naming the issue that admits it — a rule over a `def` (#525), a law that joins only through a cell completion derives (#338).
- **Size follows the sweeps.** A source stays within the per-source bounds the sweeps enforce; each sweep's ceiling states how it measures a source. Split by claim, never by count.
- **Names say the claim.** Files are kebab-case by subject and claim (`circle-group`, not `circle2`); items are the language's camelCase; a name that coincides with cubical's or the book's is kept.
- **Sugared, but where the spelling is the claim.** A corpus source is written in the sugared form `gandr fmt --form=sugared` writes: `A => B` for `+U (A -> -F B)`, `A * B` for `#{A, B}`, `def x : T = e ;` for a pair. A source whose claim is a former's own shape declares `@[ form(explicit) ]` at its head and keeps the explicit form. [`root`](src/root.rs) § The corpus names those sources and the check that holds both roots to the form. A refusal is sugared unless it is about the explicit form.
- **The strict root is strict.** `strict/` admits only `checks` and its `runs`, `normalizes`, `decomposes`, `traces`, `reads` and `distributes` refinements.

The test suite follows the same shape: one witness per behaviour, in the crate that owns it, named as the sentence it proves; a corpus-wide property is a `sweeps` module test, and nothing else walks the corpus; a setup two crates share is one function called twice; a duplicate witness is deleted when found and the survivor named in the commit.

## Comments

Write as ASD-STE100 writes. Use short sentences, one topic a paragraph, the active voice and the present tense. Keep the technical vocabulary free.

A source opens on its head. The first paragraph says what the source shows, and its first sentence holds at most twenty words. The second paragraph says why, and the third says how. A `Limits` paragraph follows only when the source has limits: what it assumes and does not check, what it does not do yet, and where it departs from the work it cites. The last paragraph holds only `- see:`, `- owes:` and `- cites: [label]` lines. The head ends on one `[label]: <URL> "<authors>, <title>"` line per label.

An item comment holds at most two sentences, and a third when it states a limit. No sentence holds more than twenty-five words. No semicolon joins two sentences. A passive is one of `is refused`, `is admitted`, `is replayed`, `is checked` and `is normalised`.

A comment answers to its reader, not to an earlier text. Keep each claim that a reader of the example needs and that the code does not state: a trust boundary, a limit, a departure from the cited work, an effect the example relies on, the reason for a choice. Drop a claim that restates the code, and detail that makes the example harder to follow. An earlier text can say too much. When a cause and its effect become two sentences, the second opens with `So`. A rewrite says in its pull request what it drops, and why.

`check:prose` reads these rules. Two sources under higher cells and desc show the shape.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Specification and adequacy, inputs not a pipeline, references | [`src/lib.rs`](src/lib.rs) |
| One predicate: settled; lockstep with the checker | [`settle`](src/settle.rs) |
| Run outcomes, the strict root, one expectation per name | [`expectation`](src/expectation.rs) |
| Sealed and the ledger size | [`report`](src/report.rs) |
| The closed refusal vocabulary, native universe-path refusals | [`refusal`](src/refusal.rs) |
| Membership, the corpus directories, the control subjects, one walk, the pending set, the sketch set | [`root`](src/root.rs) |
| The kernel export suite | [`kernel_export`](src/kernel_export.rs) |
| A comment on every fixture item, the ledger ratchet | [`src/lib.rs`](src/lib.rs), [`comments`](tests/comments.rs) |

## References

- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the refusal `FootprintsOverlap`, classed a malformed source.
- `vault:01a178aa-6cd7-7ac2-a049-ee4124ad5576` — background: the layouts design (§ layouts-semantic-abi) — the clauses `BoundaryClause` names.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design (§ The declaration) — a port at a `Type[-]` sort.
- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: `NotATranslation`, a `via` riding no flow.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: a `via` naming no flow is a malformed source.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: a flow's code is demanded by a `via` alone.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: the composite's three refusals, each a malformed source.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the presented-spaces plan (§ presented-spaces-quantities-probability) — the exact discrete semantics of a probability effect, which `distributed` settles.
- `vault:01a178aa-aa31-70c2-bdff-7d4f48020c0a` — anchor: data owns rules.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
