# gandr-theory-spec-combinators

The bounded checks a specification clause makes of state its function has accumulated.

<!-- toc -->

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Clause cost](#clause-cost)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A small `no_std` library of clause combinators: `Mark` captures a position in a sequence, `appended` returns what the sequence gained since a mark, `pushed` decides that it grew by exactly one given element, and `sorted_around` decides that a strictly increasing sequence stays so around the point a change wrote at. Each function states its bound in a `# Clause cost` section.

**Why.** An enforcing build evaluates every `#[spec]` clause on every call, so a clause that walks state accumulated across calls turns a linear run quadratic. The workspace requires a specification check to cost no more than the function it checks. The combinators let a clause speak about accumulated state while reading only what changed since a point it captured, and quenchant's `spec_clause_traversal` lint stops following a clause's calls at a function whose `# Clause cost` section states its bound.

**How.** A clause captures a `Mark` before the function runs and hands it, with the state, to a combinator after. The combinators read lengths, a suffix, a last element or two neighbours, never the whole of what was accumulated. A claim about the whole state is checked once where the state is built; a claim linear in accumulated state is not a combinator and carries a reasoned `#[expect(spec_clause_traversal, ...)]` at its own site. The decisions and their reversal are in [`src/lib.rs`](src/lib.rs).

## Provided features

- `Mark`: a position in a sequence; `Mark::of` captures a sequence's length.
- `appended(items, mark)`: the suffix of `items` at or after `mark`, borrowed.
- `pushed(items, mark, value)`: whether `items` is exactly one element longer than `mark` and ends with `value`.
- `sorted_around(items, at)`: whether the element at `at` is greater than the one before it and less than the one after it.
- `Holds`: a combinator's answer, read with `bool::from`.

## Expected features

- **The specification facade.** The combinators' own clauses are checked under `--cfg anodized_panic` like every other crate's.
- **Append-only use for `appended`.** The suffix is what the function added only when nothing before the mark changed between the capture and the check.

## Examples

```rust
use anodized::spec;
use gandr_theory_spec_combinators::Mark;
use gandr_theory_spec_combinators::appended;

struct Log
{
    entries: Vec<u32>,
}

impl Log
{
    #[spec(captures: before = Mark::of(&self.entries),
        ensures: appended(&self.entries, before).iter().all(|&entry| entry > 0))]
    fn record(&mut self, entry: u32)
    {
        self.entries.push(entry.max(1));
    }
}
```

Run the tests, then the enforcing twin with every specification checked:

```sh
cargo nextest run -p gandr-theory-spec-combinators
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-spec-combinators
```

## Clause cost

Each combinator's bound is a property its tests check over every length up to 256: `appended` compares no element, `pushed` at most one, `sorted_around` at most two. The claims are separated from the nearest wrong claim by boundary inputs: `pushed` refuses the expected last element after two pushes, `sorted_around` holds of a sequence that is out of order away from the insertion point.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
