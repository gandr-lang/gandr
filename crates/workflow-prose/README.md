# gandr-workflow-prose

The sentence rules that need a parse, which bind the comments of every tracked gandr source and the rendered diagnostics against a committed ledger of debt, and each paragraph that a change writes in the markdown documents and the Rust comments.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-prose` installs the `prose` binary, which `mise run check:prose` runs. It reads every `//!`, `///` and `//` paragraph of each `.gandr` source `git ls-files` tracks, and every rendered diagnostic under `crates/surface-render-terminal/tests/golden/`, each file's diagnostics one by one. A comment's list items, its `- see:`, `- owes:` and `- cites:` lines among them, the indented lines continuing them, and its footer lines `[label]: <URL> "<authors>, <title>"` stay unread. spaCy parses the text, and the binary judges each sentence against the rules below and each diagnostic against the procedural form. It compares the findings with `corpus/prose.ledger` and refuses a finding the ledger lacks or a ledger line no finding matches. The markdown documents keep no ledger. A change answers for each paragraph that it writes in a document since its merge base, and a finding there refuses. The body mode reads a pull request's or an issue's body under the body rules, with no ledger: `mise run body:prose` runs it, and so do `pr:open`, `issue:file` and the nightly `report:prose`.

**Why.** The style the corpus follows is ASD-STE100's: short sentences, the active voice, the present tense, no noun stacks. A reviewer misses a passive or a past tense in a dense paragraph; a parser does not. The rules need a part-of-speech tag and a dependency parse, which a pattern over the text cannot give. The ledger names the existing debt, so the check refuses new debt at once while a sweep pays the old debt down.

**How.** The binary writes the passages as JSON to `parse.py`, which runs under the interpreter of the spaCy venv that the `check:prose` task pins. The script loads `en_core_web_sm` and prints each token's text, lemma, coarse and fine tags, dependency, head and character offset. Every rule is Rust over those tokens, so a rule is tested on a sentence written by hand. Text inside backticks is code, and no rule reads it. Text inside double quotes is a quotation, and the tense rule leaves it alone. A finding's key is its file, its rule and its sentence's digest ([`ledger::Key`](src/ledger.rs)).

## Provided features

- `prose --python PATH` compares the findings under the current directory with `corpus/prose.ledger`; `--root DIR` names another repository root.
- `--write` writes the ledger from the findings instead.
- `--base REV` judges each paragraph that the change wrote since `REV` in a markdown document or in a Rust source's comments, with no ledger. [`documents`](src/documents.rs) names the documents it reads and those it leaves out. [`passage::rust`](src/passage/rust.rs) states the parts of a Rust comment that hold no prose, and the run reports the code lines in comments that it skips.
- `--override FILE...` reads the `prose-override:` lines of pull request bodies, and [`mechanical`](src/mechanical.rs) states their form and their check. `check:prose` reads the architect's sign-off of each override.
- `--cache DIR --model NAME` keeps each parse by its passage's digest, so a run parses only the texts that the cache misses. `--prune` removes each parse that the head does not hold, and `--width N` bounds the interpreters of a cold parse.
- `prose --python PATH --body FILE...` judges the bodies in the files in one parse. [`passage::body`](src/passage.rs) states a body's passages and the lines it leaves unread.
- Exit `0` when the run agrees, the ledger is written or no body breaks a rule. Exit `1` on a finding the ledger lacks, a stale line, a written paragraph's finding, an override's count that differs or a body's finding. Exit `2` on a refusal: an unreadable file, a malformed glossary, ledger or override line, a failed git read or a failed parse.

### Rules

Each finding prints its file, the line its passage starts on, the rule, the sentence and the fix.

| Rule | Fires when | Fix |
| ---- | ---------- | --- |
| `STE-3.6` | a token is `auxpass` and its head's lemma is not `refuse`, `admit`, `replay`, `check` or `normalise` | name the agent and make it the subject; a passive is allowed only as `is refused`, `is admitted`, `is replayed`, `is checked` or `is normalised` |
| `STE-3.2` | the root is past, an auxiliary is `will` or `shall`, or a `VBG` has the auxiliary `be` | state it in the present tense |
| `STE-3.4` | the auxiliary `have` heads a past participle, or a passive has a modal or `to` | use one simple verb |
| `STE-2.1` | four or more consecutive tokens are `NOUN` or `PROPN` | break the stack of nouns with a preposition or a verb |
| `STE-3.5` | a `VBG` is the root, a noun modifier, a clause or the conjunct of a verb | make the `-ing` form a finite verb |
| `STE-9.3` | a verb has a particle | use one verb |
| `STE-1.2` | a glossary lemma is not in its part of speech | use the glossary word only as its part of speech |
| `STE-6.3` | a description holds more than 25 words | split it into sentences of at most 25 words |
| `STE-5.1` | a procedure sentence holds more than 20 words | split the procedure into sentences of at most 20 words |
| `STE-5.2` | an imperative has a second imperative joined by `and` or a comma | write each instruction as a sentence |
| `STE-8.1` | a semicolon in a body or a comment has a word after it | end the first sentence and start the next |
| `STE-4.1` | an em or en dash in a body or a comment has a verb after it | end the first clause, or make the text after the dash a phrase |
| `STE-4.3` | a comment names a URL, an issue, a path, a DOI or arXiv locator, or a paper's title in a parenthesis | move it to a `- see:` line, or cite the paper as `[label]` and give its locator in the footer |
| `STE-6.6` | a comment paragraph holds more than five sentences, or an item comment more than two | split the paragraph or cut the item comment |
| `STE-6.4` | a corpus head is not four paragraphs, a references line is malformed, a `- cites:` label has no footer line, or a footer line gives no quoted title | open the source on four paragraphs, and end the head on one footer line per cited label |
| `STE-6.5` | the head's first sentence holds more than 20 words | cut the first sentence |
| `STE-5.3` | a diagnostic lacks its what, its where or an imperative | state the procedure |

A comment keeps every rule but `STE-5.3`. `STE-6.4`, `STE-6.5` and the item limit of `STE-6.6` bind a corpus source outside the features ledger. A library source and a fixture keep the other comment rules. A document and a diagnostic keep `STE-3.6`, `STE-3.2`, `STE-3.4`, `STE-2.1`, `STE-3.5`, `STE-9.3` and `STE-1.2`. A body keeps `STE-3.6`, `STE-3.2`, `STE-3.4`, `STE-6.3`, `STE-5.1`, `STE-5.2`, `STE-8.1` and `STE-4.1`. `STE-5.3` binds a diagnostic, and `STE-5.2` binds its `help:` line.

A Rust comment keeps the comment rules but `STE-6.4`, `STE-6.5` and the item limit of `STE-6.6`. `STE-4.3` reads its prose alone, because text inside backticks is code there.

The doc of `Rule` in [`rules`](src/rules.rs) maps each item of ASD-STE100 issue 9 to its gate.

The small English model misreads some technical sentences. A misreading is debt like any other finding: reword the sentence so the parse reads it, or leave the line in the ledger.

### Glossary

`corpus/glossary.toml` lists the corpus's technical words in one `[words]` table, each with the one part of speech it carries: `noun`, `verb`, `adjective` or `adverb`. A technical term keeps one meaning and no paraphrase, so a sentence that uses `replay` as a noun, when the glossary makes it a verb, is an `STE-1.2` finding. The list starts from the features ledger's names and the refusal names. Add a word when the corpus uses it with one meaning.

## Expected features

A Python interpreter that imports spaCy and `en_core_web_sm`. The `check:prose` task pins Python, `uv`, spaCy and the model wheel by URL and hash, and passes the venv's interpreter, the base and the cache. No crate links Python. The local gate runs the check, and so does the merge group: the CI lane installs the same pins and caches them, with the parse cache beside them.

## Examples

```sh
mise run check:prose
mise run check:prose --write
cargo nextest run -p gandr-workflow-prose
```

## Where the detail lives

The crate docs in `src/lib.rs` state the boundaries. `passage` reads the text, `passage::rust` cuts a Rust source's comments, `documents` lists the touched documents and reads the base's paragraphs, `mechanical` reads and applies an override, `parse` runs the script, `cache` keeps a parse by its `digest`, `rules` states each rule's clause, `glossary` reads the glossary, and `ledger` keys a finding. `gandr-workflow-debt-ledger` reads the ledger, compares the findings with it and writes it. `blake3` digests a sentence and a passage; `serde_json` and `toml` read the parse and the glossary.

## References

- `vault:01a1dbb1-8f03-73b2-bbab-a82afed5f02f` — newest: the plan of the prose gate, which gives the base's digest rule, the override and the parse cache.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
