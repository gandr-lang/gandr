# gandr-surface-corpus

The expectation language over a lowered module and its verdicts — the `checks`, `owes`, `refuses`, `runs` and `normalizes` schemas, the strict and fixture corpus roots, the settle comparison, and the report a corpus runner reads its counts from — and the language's corpus itself, under `strict/` and `fixture/`. Every `.gandr` source under `fixture/` opens with a comment, and each top-level item carries a doc comment or a line comment immediately before its attribute block; a body on the next line after its commented signature inherits that comment. `check:corpus-comments` refuses a source that does not. A ledger line is `path:name:` and sixteen hex digits of BLAKE3 over the item text, whitespace collapsed and comments and the attribute block left out, ratcheted against [`fixture/uncommented.ledger`](fixture/uncommented.ledger).

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Writing to the corpus](#writing-to-the-corpus)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `settle` takes a `CorpusRoot`, the `CoreArena` a module was lowered into, the `LoweredModule` from `gandr-surface-lowering`, and the `ModuleReport` `gandr-core-checker` returned for it, and answers a `SettleReport`: one `DeclarationReport` per declared name, stating what the name's attributes assert (`Stated`), what the name produced (`Produced`: the checker's verdict, the lowering's refusal, or the root's own refusal), and the obligations its verdict owes; plus the module's ledger size. `SettleReport::tally` sums a run into a `Tally` — declarations and fixtures by `Settlement`, the ledger size, the surviving obligations, the refusals by failure class, the run's settlement and its `Seal` — which a driver absorbs across sources, gates on, and prints.

**Why.** A corpus that only says pass or fail cannot tell a run that owes nothing from one that signed for a hole, and a corpus whose sources describe their own expected failures can describe a regression as expected. The expectation language here makes both visible: the strict root admits only `checks` and its `runs` and `normalizes` refinements, every declaration states a verdict whether it writes one or not, and every report carries the ledger size.

**How.** Attributes are read off the lowering's side table under each declared name's form keys; the five schemas are matched by their registered names, and their payloads are read as literals out of the arena. The declarations are walked in admission order in lockstep with the checker's verdicts, a lowering-refused declaration consuming none. A declaration stating a run outcome that the checker accepted is run through the `Runner` the caller hands in, and one stating a run beside a refusal — `@[ runs("5"), refuses("UnboundedLoop") ]`, settled only when both hold — is run through it refused; a data block stating a normal form has its call read under its rules by `LoweredModule::normal_form`. One equality decides each declaration; the tally counts it once. A data rule in the fixture corpus is written `<=>`, the equation; the order chooses its direction. `==>` remains where a fixture pins the direction the order must admit.

## Provided features

- `CorpusRoot` and `CorpusRoot::admit`: the two roots and the strict root's refusal of `owes` and `refuses`.
- `ExpectationSchema` and `expectation_schema::Absent`: the five schemas, matched by the registry's names.
- `Runner`, `RunSpelling` and `ran::Absent`: the run a `runs` outcome is compared against, asked of the caller, accepted or refused, and the line a `normalizes` outcome is compared against.
- `normalized_call`, `normalized_call::Absent` and `NORMAL_FORM_ARROW`: the call a `normalizes` line reads, why a line reads none, and what separates a call from its normal form.
- `Stated`, `Outcome`, `ExpectationFault` and `Membership`: what a declaration states, and why an expectation states nothing.
- `RefusalName`, `RefusalSpelling`, `refusal_name::Absent`, `Refusal` and `CorpusRefusal`: the closed refusal vocabulary and producer refusal views.
- `settle`, `SettleFault`, `Produced`, `produced_refusal::Absent`, `DeclarationReport`, `Settlement` and `Surviving`: the settle comparison; `settle_after`: a module settled after its leading declarations' reports.
- `SettleReport`, `Tally`, `SettleCounts`, `ClassCounts` and `Seal`: the report and its counts.

## Expected features

- **One arena.** The caller supplies the arena the lowering minted the module into. Payload lookup rejects absent or unsuitable literals, but arena-local identifiers do not establish provenance: an unrelated arena can reuse an identifier.
- **The module's own verdicts.** The caller supplies the checker's report for exactly the declarations the lowering did not refuse, in admission order. Missing, shifted and surplus verdicts are refused by position; matching positions alone do not establish that a report came from this module.
- **`alloc`.** The crate is `no_std` with `alloc`, and does no I/O, no file walking and no process exit.

## Examples

The crate-level doctest (`src/lib.rs`, § Example) is the example: it lowers a module of two declarations, one owing a hole and one stating the refusal it earns, checks it, settles it on the fixture root and reads the tally — settled, a ledger of one, unsealed. `cargo nextest run -p gandr-surface-corpus` runs it with the crate's tests. Source-level settlement witnesses parse, lower and check their modules; counter and formatter boundary witnesses also construct values directly to reach saturation and sink failures.

Five headline sources — `fixture/model/higher-cells/ua-corolla.gandr`, `fixture/model/identity/transport-dependent.gandr`, `fixture/model/identity/transport-path.gandr`, `fixture/model/identity/funext.gandr` and `fixture/model/identity/circle.gandr` — keep a golden of every hover beside their role goldens, as `crates/surface-grammar/tests/highlight/<source>.hover`: one line per run of positions answered alike, its span, the text, the hover text and its range. A change that moves a hover moves a line; `UPDATE_EXPECT=1 cargo nextest run -p gandr-surface-lsp --test tests -E 'test(the_headline_sources_hover_as_their_goldens)'` rewrites them, and the diff is the review.

## Writing to the corpus

The corpus is a proof library and a test suite at once, and it grows by subject, not by accretion (#435). A change that adds a source or an item is held to these rules in review.

- **One subject, one directory, one base.** A subject (`identity`, `data`, `universe`, …) is one directory under `fixture/model/`; its shared declarations — `Circle`, `Int`, `Empty`, an isomorphism every file uses — live in one base source the others import (`import "./circle-base.gandr" ;`). No two sources of one subject declare a name: `gandr-surface-dispatcher`'s `no_subject_declares_a_name_twice` refuses that, and its documentation says what counts. A new directory only when no subject owns the claim.
- **One file, one claim.** A source states one theorem family or one feature, in the order the argument runs: definitions, then laws, then what refuses. Its head says what it proves and names the source it follows — a cubical file and line, a book section — and an item that follows a named lemma keeps that name in its comment. A lemma two files need is written in the file that owns it and imported, never restated; a new item goes to the file that owns its subject before a new file is opened.
- **Every item carries its comment and its attribute.** `///` before the attribute block (`check:corpus-comments` refuses otherwise), one of `checks`, `runs`, `normalizes`, `owes`, `refuses`, or `runs` beside `refuses` for a refused program whose run is part of the claim. A refused item names its issue (`#n`) in the comment and sits beside the item it blocks; there is no `declined` fixture — a refusal the record admits is a defect to file and fix. A fix's regression is an item in the subject's file, named by its issue.
- **A refusal has a twin.** What a model source proves, `pathological/<subject>/` refuses by name, one refusal per item, the same subject directory on both sides.
- **A law sits beside what it governs.** A definition with an algebraic law — a unit, associativity, a functor's composition — states it as a `rule` of its own `data` or `theory` block, oriented by the order or by a written `==>`, so the coincidence check certifies it with the block's other rules, and a `normalizes` row fires it (`model/data/map-laws.gandr`, `model/identity/group-laws.gandr`). A law is never adjoined as an axiom: one the check cannot certify yet is refused by name in the subject's twin, naming the issue that admits it — a rule over a `def` (#525), a law that joins only through a cell completion derives (#338).
- **Size follows the sweeps.** A source stays within the per-source bounds the sweeps enforce (#416: typed when at most a kibibyte, erased within the test bound); a sweep that checks at each step measures a source by the bytes its check reads — the source laid out after its import closure — so a source over a long closure is typed nightly and erased and hovered more coarsely on the pull request (#776). Split by claim, never by count.
- **Names say the claim.** Files are kebab-case by subject and claim (`circle-group`, not `circle2`); items are the language's camelCase; a name that coincides with cubical's or the book's is kept.
- **Sugared, but where the spelling is the claim.** A fixture source is written in the sugared form `gandr fmt --form=sugared` writes, `A => B` for `+U (A -> -F B)` and `A * B` for `#{A, B}`, since that is what one writes day to day. A source whose claim is a former's own shape declares `@[ form(explicit) ]` at its head and keeps the explicit form: the arity sources (`surface/arity/` `product`, `sum`, `records`), the engine's fragment and classifier sources (`fragment/`, `classifier/`), the universe sources (`model/universe/` and `pathological/universe/`) and `model/identity/cong-thunk.gandr`, whose path lies in a thunk type. A refusal is sugared unless it is about the explicit form. `check:corpus` holds every fixture source to this with `gandr fmt --check --form=sugared`. `strict/` keeps what the printer's explicit form writes.
- **The strict root is strict.** `strict/` admits only `checks` and its `runs` and `normalizes` refinements.

The test suite follows the same shape: one witness per behaviour, in the crate that owns it, named as the sentence it proves; a corpus-wide property is a `sweeps` module test, and nothing else walks the corpus; a setup two crates share is one function called twice; a duplicate witness is deleted when found and the survivor named in the commit.

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

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
