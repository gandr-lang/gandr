# gandr-surface-diagnostics

The diagnostics model: what a refusal, an unsettled declaration, a goal, a shadowing warning and a ledger line say, decided once, as data every face projects.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The procedural form](#the-procedural-form)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `diagnose` builds one `Diagnostic` from a `Subject` — a checker refusal with the `Failure` its machine kept, an unsettled declaration, a goal, a lowering or recognition refusal, a shadowed builtin, or a ledger line — over the source text it names. A diagnostic holds its severity, identifier, message, detail, the annotations at its bytes (the primary first), the contexts it stood inside, outermost first, the hypotheses in scope, a note, a help and the excerpt of source its loci touch. `gandr-surface-render-terminal` lays one out for a terminal; `gandr-surface-lsp` publishes one to an editor; neither reads a producer's type.

**Why.** A refusal names bytes and a rule; a reader wants the line those bytes sit on and the rules the checker stood inside when it refused. Deciding that in one place keeps the terminal, the editor and a test from disagreeing about a refusal's loci and causes. The alternative, each face reading the step and the producers' refusals itself, is what this crate replaced.

**How.** A checker refusal's `Failure` names the frames the machine stood inside, each a `FrameRole` read through an exhaustive sentence table with no catch-all arm, and the term and type each frame judged. Each core node resolves through the origin table the composition kept; a frame with no recorded bytes stays a context with no locus, which a face shows as a note rather than a guessed span. The types a refusal compares are spelled by `Spellings` while the arena is at hand. Every locus is checked against the text it names before it is kept.

## Provided features

| Surface | Behavior and evidence |
| ------- | --------------------- |
| `diagnose`, `Subject`, `PATHLESS` | One diagnostic per subject, located at its term; a refusal with no recorded span claims none. |
| `Diagnostic` and its parts | `primary`, `details` per `Verbosity`, `json`; contexts carry their role's sentence, the type judged and the binders they introduce. |
| `Failures`, `TypeSpellings`, `Spellings`, `spelling`, `kept` | The machine's failure per refused body and the spelled types, kept while the arena lives, in each spelling: a face reads the one its reader chose. `TypeSpellings::after` spells a document's own refusals beside its import closure's spellings. |
| `sentence`, `Label`, `Culprit` | The frame table, the labels a locus reads as, and the culprit a lowering refusal names. |
| `Lint`, `Identifier`, `Fix` | A lint's finding, named by the lint rather than a refusal: the `explicit-exits` lint reports each inferred exit as a warning whose `fix` inserts the keyword, the edit that settles it; the `explicit-runs` lint reports each inferred run, its `fix` writing `run` before the computation, parenthesised where the computation begins a statement. |
| `advice`, `help` | The help of a refusal: one imperative sentence that tells the reader what to do. A name with no help yet is `help::Absent::Unworded`. |

## Expected features

- **A text that is the text the producer read.** A span the text cannot answer leaves its diagnostic unlocated rather than quoting the wrong line.
- **A face.** The model writes nothing; a renderer or a server projects it.

## Examples

```rust
use gandr_surface_diagnostics::Subject;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_diagnostics::report_span;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

let diagnostic = diagnose(
    std::path::Path::new("ledger.gandr"),
    SourceText::from(""),
    Subject::Ledger {
        line: "unsettled: a pending source",
        at: Maybe::Absent(report_span::Absent::Standing),
    },
);
assert_eq!(diagnostic.message.text, "unsettled: a pending source");
```

The crate's tests run with `cargo nextest run -p gandr-surface-diagnostics`; the crate-level example runs with `cargo test -p gandr-surface-diagnostics --doc`.

## The procedural form

A refusal reads as a procedure, in the form of ASD-STE100's procedures. The message states what is wrong in one sentence. The primary label names the place in one phrase. The help tells the reader what to do in one imperative sentence. A refusal that an issue tracks ends with that issue instead. The technical vocabulary is free.

`message.rs` writes the message, `locus.rs` writes the label and `advice.rs` writes the help, each with one arm per refusal name. `mise run check:prose` reads each rendered golden for the three parts and records a golden that lacks one in `corpus/prose.ledger`. The names get their help most-seen first, ten at a time (#2920).

Without a help, an unresolved name tells the reader what is wrong and where, but not what to do:

```text
error[UnresolvedName]: `missing` is not defined
  ╭▸ corpus/ledger/diagnostics/UnresolvedName.gandr:3:14
  │
3 │ def broken = missing ;
  │              ━━━━━━━ not found in this scope
```

With the help, it ends with what to do:

```text
error[UnresolvedName]: `missing` is not defined
  ╭▸ corpus/ledger/diagnostics/UnresolvedName.gandr:3:14
  │
3 │ def broken = missing ;
  │              ━━━━━━━ not found in this scope
  │
  ╰ help: define `missing`, or import the module that exports it
```

Without a help, a stray keyword puts its correction in the message as a question:

```text
error[MalformedForm]: `type` is a keyword and cannot stand here in this theory declaration; did you mean `Type`?
  ╭▸ corpus/ledger/diagnostics/MalformedForm.gandr:4:12
  │
4 │   sort M : type;
  │            ━━━━ a keyword where a term belongs
```

With the help, the message states the fault and the help gives the correction:

```text
error[MalformedForm]: `type` is a keyword and cannot stand here in this theory declaration
  ╭▸ corpus/ledger/diagnostics/MalformedForm.gandr:4:12
  │
4 │   sort M : type;
  │            ━━━━ a keyword where a term belongs
  │
  ╰ help: write `Type` instead
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The model as the one decision, its alternative and reversal, specification discipline | [`src/lib.rs`](src/lib.rs) |
| The schema | [`model`](src/model.rs) |
| Building a diagnostic from each subject | [`report`](src/report.rs) |
| The frame table | [`frame`](src/frame.rs) |
| The message and the title | [`message`](src/message.rs) |
| The help | [`advice`](src/advice.rs) |
| Labels, loci and contexts | [`locus`](src/locus.rs) |
| The culprit a lowering refusal names | [`culprit`](src/culprit.rs) |
| Spelled types and kept failures | [`spelled`](src/spelled.rs) |
| Verbosity | [`verbosity`](src/verbosity.rs) |
| Lints, `explicit-exits` and `explicit-runs` among them | [`lint`](src/lint.rs) |

## References

- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the `FootprintsOverlap` label, authority both halves of a fork hold and one may change.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
