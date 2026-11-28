# Bootstrap census

Each workspace crate with a library, measured for the first rewrite in gandr: the runtime bootstrap (#2895) rewrites one crate at a time, and this census is its first rung (#2896), the record the boundary (#2901) and the first twin read. `mise run report:bootstrap-census` prints the census: a table of the measures of each crate, the ranking, and the boundary types of the top three. The tree does not hold the census, because almost each change to a library changes it. A person writes the text of this page.

- **Public items:** the library's public items as `purposes:items` lists them, modules and the crate root left out.
- **Boundary types:** the types the crate's own public items name, in a signature, a field, a variant, an alias or a constant, each counted once; a trait implementation's own items are left out, the trait fixing their signatures. A type another crate defines must cross the rewrite's boundary as it stands.
- **Specs per item:** the specification bullets and the `- witness:` bullets of the public items' documentation, with the library's `#[spec]` attributes, over its public items.
- **Hotpath:** a function of the library is measured by `hotpath::measure`. A rewrite there answers to the runtime's speed before anything else, so it ranks after every crate that is not on the hotpath.
- **Depth:** the longest chain of workspace dependencies under the crate. A leaf, depth 0, is rewritten without rewriting anything it calls first.
- **Lines:** the library's Rust sources, test modules left out.

The ranking puts the crates off the hotpath first, then leaves before the rest, then the fewest boundary types per public item, then the most specs per item. A crate with no public item is last.

## Candidates

The top three of this census, each with the specification its twin is written to, the oracle that holds the twin to the Rust, and the types that cross the boundary (#2901). The counts measure a surface, not what crossing it takes; each paragraph names what reading the crate adds. The paragraphs are rewritten when the top three change.

### `theory-spec-combinators`

- **Specification:** the four combinators' `ensures:` clauses and `# Clause cost` bounds in `sequence.rs`: `Mark::of` reads the length, `appended` returns the suffix past a mark and reads no element, `pushed` compares at most one element, `sorted_around` at most two. `Holds` converts to and from `bool`.
- **Oracle:** the crate's witnesses under `sequence::tests`, run on the twin with the same inputs; `pushed_compares_at_most_one_element` and `sorted_around_compares_at_most_two_elements` count comparisons through a tallying element, so they hold the twin to the bound as well as the answer.
- **Boundary:** no type from another crate. Its own `Mark` and `Holds` cross as a `usize` and a `bool`.
- **What the counts miss:** every combinator is generic over `&[T]`, and 11 crates call them inside `#[spec]` clauses. A generic signature does not cross an extern boundary, so the twin fixes the element types its callers instantiate or takes the comparison as an argument, and an enforcing build pays the crossing on every checked call.

### `runtime-stencils`

- **Specification:** the L machine's transitions as the crate's root states them: one stencil per transition under the five-register `Stencil` convention, the holes, the host call, and the authoring rules (no hole a valid pointer, no two stencils with one body, no call but the host, fuel spent at every unbounded jump).
- **Oracle:** `tests/agreement.rs`, the differential between emitted native code and the portable executor, and the reading each corpus `runs` item reaches.
- **Boundary:** `core::option::Option` and `core::result::Result`, then its own `Word` (`#[repr(transparent)]` over `usize`), `Runtime` and `Instruction` (`#[repr(C)]`), and the function-pointer types `Stencil` (`extern "rust-preserve-none"`) and `Host` (`extern "C"`).
- **What the counts miss:** the stencils are Rust compiled under `preserve_none` with `become`, into the object `gandr-runtime-emitter`'s build script patches. A twin produces that object or it replaces nothing, so it waits on a gandr lowering to that convention; each `#[repr(C)]` record is an ABI-realizability obligation of the kind #2900 states.

### `kernel-conversion-trace`

- **Specification:** the decision vocabulary `ConversionDecision<Id>`, the side of every reduction and the branch at every choice point, `ReturnEta` and `Reassociate` among them; `ConversionDecision::map`'s reanchoring; and the `TraceSink` contract: `NullSink` retains nothing and counts zero, `TraceLog` appends one decision per record and counts its length, and `ACTIVITY` is known at compile time.
- **Oracle:** `tests/differential.rs`, which asserts the recording paths a suite exercised, and the witnesses `sink::tests::a_trace_log_retains_every_decision_in_order`, `sink::tests::the_null_sink_retains_nothing` and `decision::tests::reanchoring_keeps_every_branch`.
- **Boundary:** no type from another crate. Its own decision, side, position, activity and count types cross as data, the enums as tagged sums.
- **What the counts miss:** the identifier parameter `Id` and the trait `TraceSink` with its associated constant are generic, and six crates (`core-checker`, `core-nbe`, `kernel-core`, `kernel-term`, `surface-corpus`, and `theory-coherent-resolutions`' tests) instantiate them at their own identifiers. The static-dispatch discipline, recording compiled away at `NullSink`, does not survive a call through an extern boundary, and the kernel replays what this vocabulary records.
