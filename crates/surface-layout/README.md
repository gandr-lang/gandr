# gandr-surface-layout

The document-layout engine every gandr printing face resolves through: a sealed document arena, Pareto resolution with width taint, and a first-order render machine.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Executable specifications](#executable-specifications)
- [The document algebra](#the-document-algebra)
- [Resolution and the cost order](#resolution-and-the-cost-order)
- [Width taint](#width-taint)
- [Plans and the render machine](#plans-and-the-render-machine)
- [Ordered maps for the interner and the memo](#ordered-maps-for-the-interner-and-the-memo)
- [Explicit stacks](#explicit-stacks)
- [Limits and typed failures](#limits-and-typed-failures)
- [License](#license)

## Synopsis

**What.** `gandr-surface-layout` builds a document in a sealed arena, resolves it to the layout of least cost at a page width, and renders that layout as exact bytes. A client states which forms group, nest and align; the crate owns everything that must agree between clients: line emission, flattening, choice resolution, the cost order, width taint, memoization, render plans and every resource limit. It uses `core` and `alloc` under `no_std`.

**Why.** The presentation printer, a source formatter and a language-server face each print the same terms at different widths. One engine makes a layout decision in one place, so two faces never disagree about where a line breaks. The engine is more expressive than a greedy printer: it carries arbitrary choice and unaligned concatenation, which cannot be added to a greedy representation afterwards without rewriting every client document.

**How.** `DocBuilder` is the only insertion path; it interns flattened images while sealing, so `group(d)` costs one choice node over two shared children. `resolve` walks the sealed DAG on one explicit work vector, memoizing each in-bound state — a node entered at a column under an indentation — as a Pareto frontier of measures ordered by squared overflow, then line count. A state beyond the computation width answers a deferred promise instead of a frontier. The winning measure names a plan in a generational, reference-counted plan arena, and `render` executes that plan on an explicit stack into a buffer reserved once at the exact output size.

## References

- Sorawee Porncharoenwase, Justin Pombrio, and Emina Torlak. "A Pretty Expressive Printer." _Proceedings of the ACM on Programming Languages_ 7, OOPSLA2, October 2023. [doi:10.1145/3622837](https://doi.org/10.1145/3622837), [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) — the optimality theorem, the measure set and its dominance order, the computation width and the taint state machine, in-context memoization, and the complexity bounds this engine implements.
- Jean-Philippe Bernardy. "A Pretty But Not Greedy Printer (Functional Pearl)." _Proceedings of the ACM on Programming Languages_ 1, ICFP, article 6, September 2017. [doi:10.1145/3110250](https://doi.org/10.1145/3110250) — resolution as a frontier of non-dominated measures rather than a greedy first fit.
- Philip Wadler. "A Prettier Printer." In Jeremy Gibbons and Oege de Moor (editors), _The Fun of Programming_, Palgrave Macmillan, 2003. [prettier.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf) — the document algebra that this crate's choice and flattening generalize.

## Provided features

- `arena`: the sealed `DocArena`, checked `DocId` handles that refuse a foreign or out-of-range identity, newline-free `TextSource`/`TextOwned` and opaque `VerbatimSource`/`VerbatimOwned` leaves that keep LF and CRLF endings byte for byte (`algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`).
- `build`: `DocBuilder` with `text`, `verbatim`, `line`, `hard_line`, `concat`, `concat_all`, `nest`, `align`, `choice`, `flatten`, `group` and `finish`; identities are dense insertion ordinals that never move (`algebra::tests::identities_are_dense_insertion_ordinals_that_never_move`), and finalization is deterministic and idempotent (`algebra::tests::finalization_is_deterministic_across_runs`, `algebra::tests::flattening_is_idempotent`).
- `resolve`: the least-cost layout of a root with its `LayoutCost` and `WidthTaint`; bounded choice fixtures agree with direct cost enumeration (`algebra::tests::exhaustive_small_documents_match_the_direct_oracle`), and every bag of up to three candidates over nine cost/column ranks agrees with a stable pairwise Pareto oracle (`resolve::tests::small_candidate_bags_match_a_stable_pairwise_pareto_oracle`).
- `render`: the complete output of that layout, its cost and its taint, never partial output (`algebra::tests::render_text_and_layout_metadata_are_exact`, `algebra::tests::render_limits_fail_without_partial_output`).
- `limits`: `BuildLimits`/`BuildMeter` and `RenderLimits`/`RenderMeter`, each ceiling refusing exactly at its boundary (`algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`, `algebra::tests::render_limits_fail_at_each_exact_boundary`).
- `error`: `BuildError` and `RenderError`, with distinct causes, exact numeric ceilings and propagated output-sink failures, without fixing diagnostic wording (`error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`).
- `units`: the nominal widths, columns, counts and ceilings every signature is stated in.

## Expected features

A client decides which syntactic forms group, nest and align, and chooses the page width, the computation width and the physical line ending through `LayoutOptions`; the computation width is at least the page width. The client chooses the build and render ceilings; the defaults suit one document of up to a million nodes. Nothing else is required: the crate needs an allocator and no other runtime.

## Examples

Build a grouped binding, then render it at a wide and a narrow page:

```rust
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::limits::BuildLimits;
use gandr_surface_layout::limits::BuildMeter;
use gandr_surface_layout::limits::RenderLimits;
use gandr_surface_layout::limits::RenderMeter;
use gandr_surface_layout::measure::LayoutOptions;
use gandr_surface_layout::measure::PhysicalLineEnding;
use gandr_surface_layout::render::render;
use gandr_surface_layout::units::ComputationWidth;
use gandr_surface_layout::units::NestAmount;
use gandr_surface_layout::units::PageWidth;

fn main() -> Result<(), Box<dyn core::error::Error>> {
    let mut build_meter = BuildMeter::new(BuildLimits::default());
    let mut builder = DocBuilder::try_new(&mut build_meter)?;
    let head = builder.text(TextSource::from("let total ="))?;
    let value = builder.text(TextSource::from("first + second"))?;
    let line = builder.line();
    let tail = builder.concat(line, value)?;
    let body = builder.nest(NestAmount::from(2u32), tail)?;
    let joined = builder.concat(head, body)?;
    let doc = builder.group(joined)?;
    let arena = builder.finish()?;

    for (page, expected) in [
        (100u32, "let total = first + second"),
        (16u32, "let total =\n  first + second"),
    ] {
        let options = LayoutOptions::try_new(
            PageWidth::from(page),
            ComputationWidth::from(page.saturating_mul(2)),
            PhysicalLineEnding::Lf,
        )?;
        let mut meter = RenderMeter::new(RenderLimits::default());
        let rendered = render(&arena, doc, &options, &mut meter)?;
        assert_eq!(rendered.text, expected);
    }
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
cargo nextest run -p gandr-surface-layout
```

## Executable specifications

Nontrivial items pair their specification clauses with `#[spec]` predicates and an adequacy argument naming concrete witnesses. Enforcing builds check arithmetic and refusal precedence, unchanged counters after refused charges, adopted allocation identities, handle namespaces, plan generations and ownership, taint contexts, resolver transitions, Pareto ordering and exact output accounting. Predicates use bounded snapshots or borrowed observations rather than cloning owned stores or replaying callbacks.

Run the same witnesses with executable checks enabled:

```sh
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-surface-layout
```

Each `executable: none` clause names an unavailable observation: data declarations have no call boundary, formatters expose write-only sinks, the small-stack witness consumes a one-shot callback, and opaque const projections lack const value observers. Their adequacy sections identify the runtime consumers that observe the obligation. Bounded exhaustive models are distinguished from selected graph fixtures; allocator exhaustion is not claimed as exercised.

## The document algebra

A document is empty, text, verbatim text, a soft or hard line break, a concatenation, a nesting by a fixed amount, an alignment to the current column, a choice between two documents, or the flattening of one. `group(d)` is `choice(d, flatten(d))`, unflattened form on the left. Flattening turns a soft line into one space and leaves a hard line, verbatim bytes and indentation alone (`algebra::tests::flatten_turns_a_line_into_one_space`, `algebra::tests::flatten_leaves_a_hard_line_alone`).

**Concatenation is unaligned.** The right operand starts at the column the left one ends at, and its lines indent by the enclosing nesting, not by that column (`algebra::tests::concat_resolves_the_right_at_the_left_ending_column`). Alignment is a separate constructor (`algebra::tests::align_sets_indentation_to_the_current_column`).

- **Alternatives.** An aligned concatenation, the greedy printers' default, cannot express a hanging layout whose continuation returns to the enclosing indentation.
- **Reversal.** None planned: alignment is available as its own node.

**The arena is sealed and shared.** Naming a handle twice builds a shared subdocument, charged as an edge rather than a node (`algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_node`). `finish` computes every node's flattened image in one forward pass, interning each distinct image once and keeping the original identity when flattening changes nothing (`algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`).

## Resolution and the cost order

A layout's cost is the sum of squared overflow past the page width, then the number of line breaks, compared lexicographically (`algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`). A measure pairs a cost with the column the layout ends at and the plan that produces it. A state answers a frontier: measures sorted by cost, none dominated in both cost and ending column. A choice merges its branches' frontiers; a concatenation resolves its right operand at each of the left frontier's ending columns. Each in-bound state is resolved once and memoized for the rest of the resolution (`algebra::tests::shared_contexts_reuse_memo_states`).

**Squared overflow, then line count.** Overflow dominates, so no layout trades a column past the page for fewer lines; squaring spreads overflow across lines rather than piling it on one.

- **Alternatives.** Linear overflow prefers one very long line to two slightly long ones. Line count first prints everything on one line whenever any layout overflows.
- **Reversal.** A client that needs another order; the order lives in `measure` and no client may replace it today.

## Width taint

A state whose column or indentation exceeds the computation width is outside the optimality theorem. Resolution does not enter it: it answers a deferred promise that carries the state's exact node, column and indentation, and forces that promise only when no in-bound measure competes. A merge prefers any frontier over a promise, and of two promises keeps the left one unforced, so a document too wide to lay out falls back to its vertical form (`taint::tests::merge_frontier_wins_over_ready_taint`, `algebra::tests::render_tainted_root_uses_complete_left_biased_output`). A tainted result is complete output; `Rendered::width_tainted` reports the taint and never a truncation (`algebra::tests::tainted_contexts_preserve_taint_and_output`).

## Plans and the render machine

A measure names its layout as a plan: a first-order tree of text, verbatim, newline-with-indentation and sequence nodes in a generational arena. A plan identity carries its slot's generation, so a recycled slot never answers an old identity (`plan::tests::plan_generation_rejects_recycled_identity`). Plans are reference-counted; a dominated measure releases its plan when the frontier drops it, so the live-plan ceiling bounds what resolution retains.

Rendering checks the winning plan's exact byte count against the output ceiling, reserves the buffer once, and executes the plan on an explicit stack of identities. Indentation is emitted in runs of spaces from one static string. No document tree, candidate string or closure is materialized.

## Ordered maps for the interner and the memo

The flatten interner and the resolver memo are `BTreeMap`s: deterministic iteration and lookup with no hash seed, `no_std` through `alloc`, and no dependency. Their growth is bounded by the node ceiling and the memo-state ceiling, each charged before every insertion.

- **Alternatives.** `hashbrown` with `foldhash` gives constant-time lookup, a fixed seed for determinism and fallible reservation, so a failed growth becomes a typed error; it adds two dependencies to a crate that has one.
- **Reversal.** Profiling shows map lookups dominate resolution or finalization, or a consumer needs the growth of these two tables to fail as a typed error rather than through the allocator.

## Explicit stacks

Nothing in the crate recurses. Finalization is one forward pass, because every edge names an earlier node; balanced concatenation builds explicit levels; resolution runs one work vector of evaluations and continuations; releasing a plan returns its children to the caller's stack; rendering walks plan identities on a heap stack. A deep document is ordinary input: the witnesses seal spines of two hundred thousand nodes and release a chain of a hundred thousand plan sequences on a 64 KiB native stack (`algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`, `plan::tests::plan_release_recycles_a_deep_sequence_iteratively`). The resolver's and the machine's stacks have their own ceilings (`algebra::tests::render_vm_stack_limit_is_checked_before_output`).

## Limits and typed failures

Every store checks its ceiling before it grows, every counter checks its arithmetic, and a refused charge leaves the counter unchanged (`algebra::tests::a_refused_charge_leaves_the_counter_unchanged`). The defaults:

| Ceiling | Default |
| ------- | ------- |
| document nodes | 1,000,000 |
| text bytes | 64 MiB |
| verbatim lines | 1,000,000 |
| build steps | 20,000,000 |
| memo states | 1,000,000 |
| frontier entries | 4,000,000 |
| plan nodes created | 16,000,000 |
| live plan nodes | 8,000,000 |
| output bytes | 64 MiB |
| layout steps, resolver work entries, machine steps | 100,000,000 each |
| resolver stack, machine stack | 1,000,000 each |

**Broken invariants are typed.** A machine state that the resolver or the render machine never produces — a stale plan identity, a continuation without its result, a root with no measure — returns `RenderError::Invariant` naming the invariant, never a panic and never an arithmetic error borrowed for the purpose.

- **Alternatives.** A panic halts the face that printed, which a language server must not do; reporting the state as an overflow names the wrong cause.
- **Reversal.** None planned: an invariant variant is cheap and each one names a defect to fix.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
