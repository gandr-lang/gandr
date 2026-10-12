# gandr-surface-diagnostics

The renderer for what one step of the dispatcher's walk prints: each refusal, each unsettled declaration, each goal and each shadowing warning as a located source snippet, and each ledger line a verb prints beside them.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [What a report shows](#what-a-report-shows)
- [The message is the user's; the title is the producer's](#the-message-is-the-users-the-title-is-the-producers)
- [The verbosity chooses what to show, never what the report holds](#the-verbosity-chooses-what-to-show-never-what-the-report-holds)
- [The label says what the locus is](#the-label-says-what-the-locus-is)
- [A label names the types its refusal compares](#a-label-names-the-types-its-refusal-compares)
- [A refusal names the judgements it stood inside](#a-refusal-names-the-judgements-it-stood-inside)
- [A shadowed builtin is a warning](#a-shadowed-builtin-is-a-warning)
- [Native universe-path diagnostics](#native-universe-path-diagnostics)
- [The one input is the step](#the-one-input-is-the-step)
- [Every span is the producer's](#every-span-is-the-producers)
- [Context is causal](#context-is-causal)
- [The layout backend](#the-layout-backend)
- [Colour is the caller's choice](#colour-is-the-callers-choice)
- [Specification discipline](#specification-discipline)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-diagnostics` reads a `Step` of `gandr-surface-dispatcher`'s walk under the verb the walk runs and yields its entries in declaration order: a `Report` for each refusal, unsettled declaration and goal the verb prints, and a `Line` for each ledger line — a settled fixture, a pending source's refusal, a pending source the lowering reads. A report renders as a snippet: the class and message, the source's path with line and column, the lines its loci cover, each locus marked and labelled.

**Why.** A refusal names bytes, and a reader wants the line those bytes sit on. Rendering is a consumer of the step, never a second decision: the dispatcher's `shown` decides what a verb prints, and this crate decides only how. Keeping the layout here keeps the driver a process boundary and lets an editor or a test render the same report the driver prints.

**How.** `entries` walks the step's declaration reports in order and asks `shown` about each one. A report's loci come from its producer: the lowering's and the corpus root's refusals carry their spans, and a checker refusal's core nodes resolve through the origin table the step carries. Each locus is checked against the step's text, then `annotate-snippets` lays out the group with Unicode decorations, plain or styled. Witnesses are named under [Provided features](#provided-features).

## Provided features

| Surface | Behavior and evidence |
| ------- | --------------------- |
| Entry streams | Declaration order, verb filtering and persistent exhaustion. Witnesses: `diagnostics::diagnostics::each_verb_prints_its_entries`, `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`. |
| Ledger entries | Borrow the source path and add no framing terminator; literal path controls remain. The verb witness checks prefixes and semantic payloads through real walks. |
| Classification and loci | Producer classes and origin families remain distinct. Witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`. |
| Metadata | Refusal identifiers, title payloads, labelled context, the types a refusal compares and its nested reasons are available independently. Witnesses: `diagnostics::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`, `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`, `diagnostics::diagnostics::a_mismatch_label_spells_both_types`, `diagnostics::diagnostics::a_refusal_names_the_judgements_it_stood_inside`. |
| Rendering | Refusal, unsettled and goal layouts, and a refusal with nested reasons, have consumer-visible golden witnesses; pathless sources and duplicate-signature context have location assertions. |
| Verbosity | One refusal is pinned at every level, the JSON image parsed back. Witness: `diagnostics::diagnostics::one_refusal_renders_at_every_verbosity`; ledger lines at the JSON level: `diagnostics::diagnostics::each_verb_prints_its_entries`. |
| Styling | Both terminal capabilities have exact style observations; forced styling preserves plain glyphs after removing backend SGR controls. Witness: `diagnostics::diagnostics::forced_styling_colors_actual_facade_annotations`. |

## Expected features

- **A step whose text is the text it composed.** `Step::Source` carries both; a span the text cannot answer leaves its report unlocated rather than quoting the wrong line.
- **A writer.** Rendering adds no framing terminator; the caller chooses the separator. Literal path controls can include a final line feed or carriage return. `Rendered::from(String)` preserves supplied bytes.
- **Terminal detection, if colour is wanted.** The caller states whether its output is a terminal; the crate reads no environment.

## Examples

```rust
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use quenchant_shape::shape::Maybe;

let verb = Verb::Check(Goals::Gated);
let mut walk = Walk::new(vec![std::path::PathBuf::from("broken.gandr")]);
while let Maybe::Present(step) = walk.step() {
    for entry in entries(&step, verb) {
        println!("{}", entry.render(RenderStyle::Plain, Verbosity::User));
    }
}
```

The crate's tests run with `cargo nextest run -p gandr-surface-diagnostics`; the crate-level example runs with `cargo test -p gandr-surface-diagnostics --doc`.

## What a report shows

| Kind | First line | Primary locus and label | Note |
| ---- | ---------- | ----------------------- | ---- |
| refusal | `error[<refusal>]: <message>` | the refusal's span, labelled with what the bytes there are | the declaration, what it states and its surviving obligations |
| unsettled declaration | ``error: `<name>` states …; produced …`` | the declaration, labelled with how it is unsettled | none |
| goal | ``goal: `<name>` states …; produced …`` | the declaration, labelled with its surviving obligations | none |
| source refused as a whole | `error[<refusal>]: the source is not a list of declarations: …` | the refusal's span, labelled with what the bytes there are | none |
| shadowed builtin | ``warning[ShadowedBuiltin]: `<path>` shadows a builtin name; the source's binding wins`` | the shadowing name, labelled `shadows a builtin` | none |

The refusal name in the first line is the spelling the corpus's `refuses` attribute states, so a reader can copy it into an expectation. A type mismatch renders as:

```text
error[TypeMismatch]: mismatched types
  ╭▸ mismatch.gandr:2:13
  │
1 │ def wrong : Integer ;
  │             ─────── the type it is checked against
2 │ def wrong = "text" ;
  │             ━━━━━━ its type does not convert: expected `Integer`, found `String`
  │
  ╰ note: unsettled `wrong` states checks owing 0
```

No message carries a byte range: the snippet's path, line and column locate the refusal, and an offset beside them is noise. Mismatch labels name causal roles, such as checked-against or synthesised type, while origins locate those roles in source. Labels expose no core node addresses. An empty path renders as `<input>`. A pending source's ledger line has no snippet, so it keeps the refusal's byte range after the producer's text.

## The message is the user's; the title is the producer's

Each producer words its refusals for whoever reads its code: the lowering names the grammar's sorts (`` `hole` has an operand where it takes none ``), the checker its rules (`the rule here requires a thunk type`). A report keeps that text as `Report::title` and leads with `Report::message` instead: one plain message per refusal variant, chosen by an exhaustive match in `message.rs`, naming the source's own names and its forms in words (`this hole has an operand it does not take`, `expected a thunk type`, `` `missing` is not defined ``), and naming no grammar sort, node or admission position. A refusal only a producer's broken invariant reaches says `internal error:`. Every other report's message is its title, which is already the user's. The terminal and the language server both lead with the message; the title stays for a face that wants the producer's words, the verbosity levels in particular.

The alternative was rewording each producer's `Display`, which would leave the implementer text nowhere: the lowering's and the checker's own tests, ledger lines and a detailed verbosity read it. Reversal: when no face reads the producer's text, the two collapse into one. Witness: `message::tests::every_refusal_name_has_a_plain_message`, which builds one refusal of every vocabulary name and holds each message to one line with no grammar sort.

## The verbosity chooses what to show, never what the report holds

`Report::render` and `Entry::render` take a `Verbosity`, and every level renders the same report:

| Level | Adds |
| ----- | ---- |
| `User`, the default | the message, the labels, the nested reasons and the note |
| `Detailed` | `class:` the report's class, `detail:` the producer's own wording where it differs from the message, `expression:` the primary locus's source text when it is one line |
| `Debug` | `spans:` the byte span of every locus, `refusal:` and `judgements:` the producer's refusal and the judgements it stood inside, as their implementers print them, core ids included |
| `Json` | instead of the snippet, one line of JSON: `level`, `name`, `class`, `message`, `title`, `path`, `primary`, `context`, `reasons` and `note`, each locus with its bytes, its one-based line and column in characters and its label; a ledger line is `{"level":"line","path":…,"line":…}` |

The added lines close the snippet beside the note, so a reader at the detailed level reads the user's report first. The refusal name stays on the first line at every level: a user copies it into a `refuses` expectation. The typing context a refusal stood in is not shown at any level: the step carries the judgements, not the bindings in scope at them, and showing it waits for the checker to report them. The JSON image ignores the style.

The alternative was a separate renderer per level, which would let two levels disagree about what a report holds; and a JSON image derived from the producers' own types, which would make every producer's internal layout a wire format. Reversal: a face that needs a fact no level shows adds it to the level that owns it here. Witnesses: `diagnostics::diagnostics::one_refusal_renders_at_every_verbosity`, which pins one refusal at every level and parses the JSON image back.

## The label says what the locus is

The title names the refusal and the class sorts it, so the primary label spends the underline on the bytes themselves: `not found in this scope` under a name nothing binds, `its type does not convert` under a mismatched term, `missing }` where a closer was never written. `Culprit` holds one label per refusal variant, chosen by an exhaustive match, so a new refusal cannot render until it says what its locus is. `Report::label` exposes the primary label as a `PrimaryLabel` and `Report::note` the declaration note, so a face that lays out its own message — the language server's — composes the same parts the terminal prints.

The alternative was the failure class as the label, which repeats what the title already sorted and gives every malformed-source refusal one underline whatever its cause. Reversal: when refusals carry their own per-site labels, the table gives way to them.

## A label names the types its refusal compares

A checker refusal that sets a type against another — a type, sort, level or family-argument mismatch — or meets a type of the wrong shape names those types as nodes, and a type the checker synthesised has no origin to mark. The primary label therefore carries them after its text: ``its type does not convert: expected `Integer`, found `String` ``, ``its type is not of the required shape: found `Integer` ``. The types are the ones the dispatcher spelled at the judgement, through the printer the REPL and the language server's hover share, and `Report::comparison` exposes them as a `Comparison` of an expected and a found side, each absent when the refusal names no type there or none could be spelled on one line. A refusal that compares nothing keeps its label as it was.

The alternatives were a note after the snippet, which the reader meets after the underline it explains, and the types in the title, which the checker's `Display` words without the spellings. Each [nested reason](#a-refusal-names-the-judgements-it-stood-inside) spells the type its own judgement was checked against, so the primary label keeps only the failing comparison. Reversal: a type whose spelling needs more than one line, left unspelled today, moves to a note under the snippet.

## A refusal names the judgements it stood inside

A refused body's trail, kept by the dispatcher, is the value and computation judgements the refusal stood inside, outermost first. `Report::reasons` reads each one whose term the origin table locates as a `Reason`: the term's bytes and how it was judged — checked against a type, spelled where the dispatcher could spell it, or synthesised. The snippet marks each as a context locus labelled with a `while` clause, so a force of an integer inside a thunk renders as:

```text
error[ShapeMismatch]: expected a thunk type `+U C`
  ╭▸ force.gandr:2:23
  │
2 │ def a = thunk { force 1 } ;
  │         ┬───────┬─────┯──
  │         │       │     │
  │         │       │     its type is not of the required shape: found `Integer`
  │         │       while checking this against `-F Integer`
  │         while checking this against `+U (-F Integer)`
  │
  ╰ note: unsettled `a` states checks owing 0
```

A reason at the primary locus, or at bytes an outer reason already marks, says nothing the snippet does not, and is left out, so a body refused where it stands has none; a term with no origin is left out rather than located at a guess. The language server publishes the same reasons as related information.

The alternatives were a `note: while …` line per reason after the snippet, which repeats the source position in prose where the snippet can point at it, and a reason per machine frame, which names the rule waiting on a subterm but not the subterm's own bytes. Reversal: a reason with no locus worth showing — a term only the lowering minted — becomes a note when a reader needs it.

## A shadowed builtin is a warning

Under the default warn-and-allow shadow policy, a top-level declaration or a binder named after a builtin wins, and the lowering records the shadowing with the bytes of the name. Under `check` each record is a `Report` of class `Class::Warning`, printed before the source's declaration reports in the order shadowed; `test` prints none, because its ledger records settlements. A warning settles nothing and unsettles nothing, so `gandr check` still exits zero on a source whose only reports are warnings:

```text
warning[ShadowedBuiltin]: `add` shadows a builtin name; the source's binding wins
  ╭▸ shadow.gandr:1:5
  │
1 │ def add : Integer ;
  ╰╴    ━━━ shadows a builtin
```

The identifier is `ShadowedBuiltin`, the refusal the reject policy files for the same bytes, so one name reads the same fact under either policy. The recorded design is the prior implementation's: a warning naming the shadowed path at the shadowing site. The change is the identifier: there it was a separate warning code, and a second vocabulary for one fact would have a reader learn two names. Reversal: a warning that is not a would-be refusal gets its own vocabulary. Witness: `diagnostics::diagnostics::a_shadowed_builtin_renders_as_a_warning`.

## Native universe-path diagnostics

A checker `PathCode` refusal retains its code-node locus and malformed-source class. Shape diagnostics can name the expected sum or `Path_U` classifier; injection and case remain checking forms, not unsupported language constructs. A missing origin remains an absent annotation rather than an invented source span.

**Choice.** Project the same typed refusal and causal roles used by ordinary checking, rather than add a second universe-specific diagnostic pipeline. The renderer certifies neither the candidate path nor its evidence. **Reversal.** A source notation may supply more precise origins; it must not change the refusal’s semantic class or infer certificate equality from its displayed maps.

## The one input is the step

`entries` reads the whole `Step` under its verb. A declaration and the refusal it produced are one `DeclarationReport`, so every refusal the walk carries reaches the renderer with its declaration; a face reading refusals from a list kept beside the declarations could drop one. The step carries the three things rendering needs and the composition already had: the source's text, borrowed; the lowering's origin table, moved out of the lowered module once checking is done; and the spellings of the types its checker refusals compare, made while the arena was at hand.

Passing text separately while exposing the composed module would split one fact across calls that must agree. The choice reverses if a consumer needs to render a source it never walked; such a consumer needs a constructor taking text and origins together.

## Every span is the producer's

A lowering refusal and a corpus refusal carry their spans. A checker refusal names core nodes; the origin table maps each node the lowering minted back to the syntax it came from. A node the table records nothing for leaves its locus absent, and a report with no primary locus names its source's path and quotes no line. Each span is checked against the step's text before it is laid out: a span outside the text, or one splitting a character, is unlocated, never clamped. Nothing searches the text for a plausible locus, and nothing widens an absent one to the whole declaration: a guessed locus misleads where an honest absence only fails to help.

## Context is causal

A report marks a second locus only when it is part of the cause: the earlier signature a duplicate repeats, the type a term is checked against, the type a term synthesises, the expected shape a former meets. Padding a snippet with every nearby node would make the cause harder to find, not easier. A context locus keeps its own span and its own label.

## The layout backend

The snippet layout is [`annotate-snippets`](https://docs.rs/annotate-snippets/0.12.16) 0.12.16, maintained by the Rust project and used by rustc and cargo, with default features off. It adds three crates to the graph — `annotate-snippets`, `anstyle`, which `clap` already brings, and `unicode-width` — and builds without `std`, so a rendering is a `String` and nothing else. None of its types crosses this crate's API.

| Candidate | Why it lost |
| --------- | ----------- |
| [`codespan-reporting`](https://docs.rs/codespan-reporting/0.13.1) 0.13.1 | the closest second: two crates, but colour goes through `termcolor` or a hand-written style writer, and its file database answers lookups fallibly where the step already holds the text |
| [`ariadne`](https://docs.rs/ariadne/0.6.0) 0.6.0 | one maintainer, its GitHub repository archived on a move to another host, and `yansi` always linked |
| [`miette`](https://docs.rs/miette/7.6.0) 7.6.0 | the graphical handler needs `fancy-base`, about thirty crates including `syn`, and reports must implement its `Diagnostic` trait |

The choice reverses on a security advisory or an unmaintained notice against `annotate-snippets`, on the Rust project ceasing to use it, or on a release that drops plain rendering or the `std`-free build; `codespan-reporting` is next.

## Colour is the caller's choice

`RenderStyle::Plain` adds no escape sequences. `RenderStyle::Styled` adds the backend's palette. `RenderStyle::for_terminal` maps the supplied terminal capability to a style; it reads no environment variable and probes no stream.

Paths retain literal control characters in both styles. This preserves source identity without introducing a path-escaping policy; style selection offers no terminal-sanitization guarantee. An unlocated report whose path ends in a line feed or carriage return retains that final control. Witness: `report::tests::literal_path_controls_are_not_styling_or_framing`.

## Specification discipline

Nontrivial items carry executable predicates and bounded `# Adequacy` claims. Borrowed identity checks avoid copying or scanning source text. Enforcing tests exercise span validity and causal labels alongside iterator progress and numeric payload roles. The nontrivial `Display` methods state an exemption: `fmt::Formatter` exposes neither its output buffer nor an independent destination-failure observer.

The finite witnesses include UTF-8 splits and end-of-file spans. Invalid primary and context loci retain their distinct absence reasons; no span is clamped. The rendering goldens are layout examples, not exhaustive backend coverage. Each item's Rustdoc states its domain and links its own-crate witnesses.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
