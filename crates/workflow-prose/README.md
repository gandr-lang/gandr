# gandr-workflow-prose

The sentence rules that need a parse, held over the comments of every tracked gandr source, the rendered diagnostics and the crate READMEs, against a committed ledger of debt.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-prose` installs the `prose` binary, which `mise run check:prose` runs. It reads every `//!`, `///` and `//` paragraph of each `.gandr` source `git ls-files` tracks, every prose paragraph of `crates/*/README.md`, and every rendered diagnostic under `crates/surface-render-terminal/tests/golden/`, each file's diagnostics one by one. A comment's list items, its `- see:` and `- owes:` lines among them, and the indented lines continuing them stay unread. spaCy parses the text, and the binary judges each sentence against the rules below and each diagnostic against the procedural form. It compares the findings with `corpus/prose.ledger` and refuses a finding the ledger lacks or a ledger line no finding matches. The body mode reads a pull request's or an issue's body under the body rules, with no ledger: `mise run body:prose` runs it, and so do `pr:open`, `issue:file` and the nightly `report:prose`.

**Why.** The style the corpus follows is ASD-STE100's: short sentences, the active voice, the present tense, no noun stacks. A reviewer misses a passive or a past tense in a dense paragraph; a parser does not. The rules need a part-of-speech tag and a dependency parse, which a pattern over the text cannot give. The ledger names the existing debt, so the check refuses new debt at once while a sweep pays the old debt down.

**How.** The binary writes the passages as JSON to `parse.py`, which runs under the interpreter of the spaCy venv that the `check:prose` task pins. The script loads `en_core_web_sm` and prints each token's text, lemma, coarse and fine tags, dependency, head and character offset. Every rule is Rust over those tokens, so a rule is tested on a sentence written by hand. Text inside backticks is code, and no rule reads it. Text inside double quotes is a quotation, and the tense rule leaves it alone. A finding's key is its file, its rule and the first sixteen hexadecimal digits of its sentence's BLAKE3 digest. Moving a sentence keeps its key; rewording it retires the key.

## Provided features

- `prose --python PATH` compares the findings under the current directory with `corpus/prose.ledger`; `--root DIR` names another repository root.
- `--write` writes the ledger from the findings instead.
- `prose --python PATH --body FILE...` judges the bodies in the files in one parse. A body's passages are its paragraphs and its list items. A code block, a table, a heading, a quotation, an HTML comment and the block between the `quenchant-obligations` markers stay unread. An item of a mechanism's form, a head, a dash and an answer, is read from its answer.
- Exit `0` when the findings and the ledger agree, the ledger is written or no body breaks a rule, `1` when they disagree or a body breaks a rule, and `2` on a refusal: an unreadable file, a malformed glossary or ledger line, or a failed parse.

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
| `STE-4.3` | a comment names a URL, an issue or a path | move it to a `- see:` line |
| `STE-6.6` | a comment paragraph holds more than five sentences, or an item comment more than two | split the paragraph or cut the item comment |
| `STE-6.4` | a corpus head is not four paragraphs, or a references line is malformed | open the source on four paragraphs |
| `STE-6.5` | the head's first sentence holds more than 20 words | cut the first sentence |
| `STE-5.3` | a diagnostic lacks its what, its where or an imperative | state the procedure |

A comment keeps every rule but `STE-5.3`. `STE-6.4`, `STE-6.5` and the item limit of `STE-6.6` bind a corpus source outside the features ledger. A library source and a fixture keep the other comment rules. A README and a diagnostic keep `STE-3.6`, `STE-3.2`, `STE-3.4`, `STE-2.1`, `STE-3.5`, `STE-9.3` and `STE-1.2`. A body keeps `STE-3.6`, `STE-3.2`, `STE-3.4`, `STE-6.3`, `STE-5.1`, `STE-5.2`, `STE-8.1` and `STE-4.1`. `STE-5.3` binds a diagnostic, and `STE-5.2` binds its `help:` line.

### Issue 9

The gate is ASD-STE100 with unrestricted technical vocabulary. A finding names the rule it holds. A reader checks a rule the parse cannot read.

| Item | Gate |
| ---- | ---- |
| 1.1 | review: no dictionary in the tree |
| 1.2 | partial: `STE-1.2` |
| 1.3 | review: meaning needs a reader |
| 1.4 | review: a dictionary form is not in the tree |
| 1.5 | review: a technical category needs an owner |
| 1.6 | review: a technical noun needs an owner |
| 1.7 | partial: `STE-1.2` |
| 1.8 | review: a subject field needs an owner |
| 1.9 | review: ease needs a reader |
| 1.10 | review: no slang list in the tree |
| 1.11 | review: identity needs the document |
| 1.12 | review: a technical verb needs an owner |
| 1.13 | partial: `STE-1.2` |
| 1.14 | review: no spelling map in the tree |
| 2.1 | gated: `STE-2.1` |
| 2.2 | review: first form needs document order |
| 3.1 | review: a dictionary form is not in the tree |
| 3.2 | partial: `STE-3.2` reads the past, the future and the progressive |
| 3.3 | review: an adjectival `-ing` needs a reader |
| 3.4 | partial: `STE-3.4` reads the perfect and a passive after a modal |
| 3.5 | partial: `STE-3.5` |
| 3.6 | partial: `STE-3.6` |
| 3.7 | partial: `STE-1.2` |
| 4.1 | partial: `STE-4.1` reads a dash before a clause |
| 4.2 | review: a contraction needs a reader |
| 4.3 | partial: `STE-4.3` reads a reference in comment prose |
| 4.4 | review: topic relation needs a reader |
| 4.5 | review: article use needs a reader |
| 5.1 | gated: `STE-5.1` |
| 5.2 | partial: `STE-5.2` reads two imperatives joined by `and` or a comma, and a reader admits two acts at the same time |
| 5.3 | partial: `STE-5.3` |
| 5.4 | review: a condition's relevance needs a reader |
| 5.5 | review: a note's command needs a reader |
| 6.1 | review: information order needs a reader |
| 6.2 | review: logical structure needs a reader |
| 6.3 | gated: `STE-6.3` |
| 6.4 | partial: `STE-6.4` reads the four paragraphs of a corpus head |
| 6.5 | partial: `STE-6.5` reads the length of a head's first sentence |
| 6.6 | partial: `STE-6.6` holds five sentences, and two in an item comment |
| 7.1 | review: a safety heading needs a reader |
| 7.2 | review: a safety block needs a reader |
| 7.3 | review: a risk needs a reader |
| 8.1 | gated: `STE-8.1` |
| 8.2 | review: related words need a reader |
| 8.3 | review: a parenthesis needs a reader |
| 8.4 | review: a colon in a count needs a reader |
| 8.5 | review: a parenthesis in a count needs a reader |
| 8.6 | review: a token class in a count needs a reader |
| 8.7 | review: a hyphen in a count needs a reader |
| 9.1 | review: a replacement needs an earlier text |
| 9.2 | review: a sense needs a dictionary |
| 9.3 | partial: `STE-9.3` reads a verb with a particle |
| 9.4 | review: style needs the document |
| GR-1 | review: `that` needs a reader |
| GR-2 | review: `with` needs a reader |
| GR-3 | review: a pronoun needs a reader |
| GR-4 | review: `this` needs a reader |
| GR-5 | review: a false friend needs a reader |
| GR-6 | review: no abbreviation list in the tree |
| GR-7 | review: no inclusive-language list in the tree |
| GR-8 | review: a possessive needs a reader |

The small English model misreads some technical sentences. A misreading is debt like any other finding: reword the sentence so the parse reads it, or leave the line in the ledger.

### Glossary

`corpus/glossary.toml` lists the corpus's technical words in one `[words]` table, each with the one part of speech it carries: `noun`, `verb`, `adjective` or `adverb`. A technical term keeps one meaning and no paraphrase, so a sentence that uses `replay` as a noun, when the glossary makes it a verb, is an `STE-1.2` finding. The list starts from the features ledger's names and the refusal names. Add a word when the corpus uses it with one meaning.

## Expected features

A Python interpreter that imports spaCy and `en_core_web_sm`. The `check:prose` task pins Python, `uv`, spaCy and the model wheel by URL and hash, and passes the venv's interpreter. No crate links Python. The local gate runs the check, and so does the merge group: the CI lane installs the same pins and caches them.

## Examples

```sh
mise run check:prose
mise run check:prose --write
cargo nextest run -p gandr-workflow-prose
```

## Where the detail lives

The crate docs in `src/lib.rs` state the boundaries. `passage` reads the text, `parse` runs the script, `rules` states each rule's clause, `glossary` reads the glossary, and `ledger` keys a finding. `gandr-workflow-ledger` reads the ledger, compares the findings with it and writes it. `blake3` digests a sentence; `serde_json` and `toml` read the parse and the glossary.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
