# gandr-workflow-ledger

The debt ledger two workflow gates share: the findings a gate has committed to owe, one key per line. The gate refuses a new finding, and a fixed one leaves its line stale. It sits in the workflow category, outside the language, and guards neither integrity nor validity.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-ledger` is a library. `Ledger::read` reads a ledger's text, `Ledger::check` compares a check's findings with it, and `write` gives the text that regenerates it.

**Why.** The corpus comment gate (`corpus/uncommented.ledger`) and the prose check (`corpus/prose.ledger`) keep the same discipline: a finding the ledger holds passes, a new one refuses, a held line no finding carries is stale and refuses, and a write mode regenerates the file. Each kept its own reader, comparison and writer; one module gives both the same reading and the same verdict.

**How.** The ledger is generic over its key, which reads from a line, writes back as one and orders. The comment gate keys an item by its path, name and digest with the kind beside it, as a line of text; the prose check by path, rule and sentence digest. A key holds no line number, so a moved finding keeps its key. What a check prints for a new finding or a stale line stays with the check.

## Provided features

- `Ledger::read` trims each line, skips a blank or `#` line, and reads a key from each other line; `LedgerError::Unread` names the first line no key reads from.
- `Ledger::check` gives a `Verdict`: the first finding of each key the ledger lacks, in the findings' order, and each held key no finding carries, in key order.
- `write` writes a header as `#` lines, then each distinct key once, in key order, every line ended by a newline.

## Expected features

None: the caller reads and writes the file.

## Examples

```sh
cargo nextest run -p gandr-workflow-ledger
```

## Dependencies

None beyond the standard library.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
