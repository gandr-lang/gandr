# gandr-workflow-prose

The sentence rules that need a parse, held over the corpus comments, the rendered diagnostics and the crate READMEs, against a committed ledger of debt.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-prose` installs the `prose` binary, which `mise run check:prose` runs. It reads every `///` paragraph of the corpus's `.gandr` sources, every prose paragraph of `crates/*/README.md`, and every rendered diagnostic under `crates/surface-render-terminal/tests/golden/`, each file's diagnostics one by one. spaCy parses the text, and the binary judges each sentence against the rules below and each diagnostic against the procedural form. It compares the findings with `corpus/prose.ledger` and refuses a finding the ledger lacks or a ledger line no finding matches.

**Why.** The style the corpus follows is ASD-STE100's: short sentences, the active voice, the present tense, no noun stacks. A reviewer misses a passive or a past tense in a dense paragraph; a parser does not. The rules need a part-of-speech tag and a dependency parse, which a pattern over the text cannot give. The ledger names the existing debt, so the check refuses new debt at once while a sweep pays the old debt down.

**How.** The binary writes the passages as JSON to `parse.py`, which runs under the interpreter of the spaCy venv that the `check:prose` task pins. The script loads `en_core_web_sm` and prints each token's text, lemma, coarse and fine tags, dependency, head and character offset. Every rule is Rust over those tokens, so a rule is tested on a sentence written by hand. Text inside backticks is code, and no rule reads it. Text inside double quotes is a quotation, and the tense rule leaves it alone. A finding's key is its file, its rule and the first sixteen hexadecimal digits of its sentence's BLAKE3 digest. Moving a sentence keeps its key; rewording it retires the key.

## Provided features

- `prose --python PATH` compares the findings under the current directory with `corpus/prose.ledger`; `--root DIR` names another repository root.
- `--write` writes the ledger from the findings instead.
- Exit `0` when the findings and the ledger agree or the ledger is written, `1` when they disagree, and `2` on a refusal: an unreadable file, a malformed glossary or ledger line, or a failed parse.

### Rules

Each finding prints its file, the line its passage starts on, the rule, the sentence and the fix.

| Rule | Fires when | Fix |
| ---- | ---------- | --- |
| `Passive` | a token is `auxpass` and its head's lemma is not `refuse`, `admit`, `replay`, `check` or `normalise` | name the agent and make it the subject; a passive is allowed only as `is refused`, `is admitted`, `is replayed`, `is checked` or `is normalised` |
| `Tense` | the root is tagged `VBD`, or `VBN` without a present-tense `auxpass` child | state it in the present tense |
| `NounStack` | four or more consecutive tokens are `NOUN` or `PROPN` | break the stack of nouns with a preposition or a verb |
| `IngMain` | the root is tagged `VBG` | make the main verb a finite verb, not an `-ing` form |
| `Glossary` | a token's lemma is in the glossary and its coarse tag is not the glossary's part of speech | use the glossary word only as its part of speech, or choose another word |
| `Procedure` | a rendered diagnostic labels no span, or ends with no `help:` line and no note naming an issue, or its `help:` line does not start with an imperative | state what is wrong in the headline, label the span, and end with an imperative `help:` or the issue that tracks it |

The small English model misreads some technical sentences. A misreading is debt like any other finding: reword the sentence so the parse reads it, or leave the line in the ledger.

### Glossary

`corpus/glossary.toml` lists the corpus's technical words in one `[words]` table, each with the one part of speech it carries: `noun`, `verb`, `adjective` or `adverb`. A technical term keeps one meaning and no paraphrase, so a sentence that uses `replay` as a noun, when the glossary makes it a verb, is a `Glossary` finding. The list starts from the features ledger's names and the refusal names. Add a word when the corpus uses it with one meaning.

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
