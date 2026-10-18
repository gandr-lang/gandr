# gandr-surface-layout

The document-layout engine every gandr printing face resolves through: a sealed document arena, Pareto resolution with width taint, and a first-order render machine.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-layout` builds a document in a sealed arena, resolves it to the layout of least cost at a page width, and renders that layout as exact bytes. A client states which forms group, nest and align; the crate owns everything that must agree between clients: line emission, flattening, choice resolution, the cost order, width taint, memoization, render plans and every resource limit. It uses `core` and `alloc` under `no_std`.

**Why.** The presentation printer, a source formatter and a language-server face each print the same terms at different widths. One engine makes a layout decision in one place, so two faces never disagree about where a line breaks. The engine is more expressive than a greedy printer: it carries arbitrary choice and unaligned concatenation, which cannot be added to a greedy representation afterwards without rewriting every client document.

**How.** `DocBuilder` is the only insertion path; it interns flattened images while sealing, so `group(d)` costs one choice node over two shared children. `resolve` walks the sealed DAG on one explicit work vector, memoizing each in-bound state — a node entered at a column under an indentation — as a Pareto frontier of measures ordered by squared overflow, then line count. A state beyond the computation width answers a deferred promise instead of a frontier. The winning measure names a plan in a generational, reference-counted plan arena, and `render` executes that plan on an explicit stack into a buffer reserved once at the exact output size.

## Provided features

- `arena`: the sealed `DocArena`, checked `DocId` handles that refuse a foreign or out-of-range identity, newline-free `TextSource`/`TextOwned` and opaque `VerbatimSource`/`VerbatimOwned` leaves that keep LF and CRLF endings byte for byte (`tests::algebra::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`).
- `build`: `DocBuilder` with `text`, `verbatim`, `line`, `hard_line`, `concat`, `concat_all`, `nest`, `align`, `choice`, `flatten`, `group` and `finish`; identities are dense insertion ordinals that never move (`tests::algebra::identities_are_dense_insertion_ordinals_that_never_move`), and finalization is deterministic and idempotent (`tests::algebra::finalization_is_deterministic_across_runs`, `tests::algebra::flattening_is_idempotent`).
- `resolve`: the least-cost layout of a root with its `LayoutCost` and `WidthTaint`; bounded choice fixtures agree with direct cost enumeration (`tests::algebra::exhaustive_small_documents_match_the_direct_oracle`), and every bag of up to three candidates over nine cost/column ranks agrees with a stable pairwise Pareto oracle (`resolve::tests::small_candidate_bags_match_a_stable_pairwise_pareto_oracle`).
- `render`: the complete output of that layout, its cost and its taint, never partial output (`tests::algebra::render_text_and_layout_metadata_are_exact`, `tests::algebra::render_limits_fail_without_partial_output`).
- `limits`: `BuildLimits`/`BuildMeter` and `RenderLimits`/`RenderMeter`, each ceiling refusing exactly at its boundary (`tests::algebra::each_build_ceiling_refuses_exactly_at_its_boundary`, `tests::algebra::render_limits_fail_at_each_exact_boundary`).
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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Executable specifications, explicit stacks, references | [`src/lib.rs`](src/lib.rs) |
| The document algebra | [`arena`](src/arena.rs) |
| Resolution and the cost order | [`resolve`](src/resolve.rs) |
| Width taint | [`taint`](src/taint.rs) |
| Plans and the render machine | [`plan`](src/plan.rs) |
| Ordered maps for the interner and the memo | [`build`](src/build.rs) |
| Limits and typed failures | [`limits`](src/limits.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
