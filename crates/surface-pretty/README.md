# gandr-surface-pretty

The presentation printer: a checked core type, a normal-form value or an elaborated body, written in a surface spelling — sugared or explicit — and laid out at a page width through `gandr-surface-layout`.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `present_type`, `present_value` and `present_computation` take a `Source` — a store that answers, for one node, the `Former` it carries — a root, a `PageWidth` and a `Form`, and return a `Presentation`: the laid-out text and its `Fidelity`, which says whether every node was written in full. `CoreSource` reads the core arena and `ContentSource` an incremental checkpoint's content table; a face with a store of its own implements `Source` beside them. The crate uses `core` and `alloc` under `no_std`.

**Why.** A transcript line, a hover and a diagnostic operand each name a type or show a value, and each must say it the same way, in the syntax a reader can type back. One producer of that spelling, laid out by one engine, keeps every face in agreement on both the words and where a line breaks. The sugared form writes the sugar a reader writes — `A => B`, `A * B`, `A + B`, `C & D`, `(a, b)` — where the core's shape is exactly the one it stands for; the explicit form writes the formers the core is made of.

**How.** The walk reads the root's former, spells it or schedules its children, and joins their documents on an explicit task stack. Every break point is a choice between the byte the one-line spelling carries there and a line break, so a page the one-line spelling fits selects it unchanged; the layout engine chooses among the rest by least overflow, then fewest lines. A pre-scan over the same nodes collects the names a type mentions, so a generated binder name never shadows one.

## Provided features

- `present_type`: a value or computation type at a page width. Witnesses: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`, `tests::goldens::n_ary_products_and_sums_spell_between_their_braces`, `tests::goldens::records_spell_their_fields_in_label_order`, `tests::goldens::universes_spell_their_sort_and_level`, `tests::goldens::dependent_function_type_breaks_before_codomain`, `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`, `tests::goldens::arrow_chain_breaks_before_each_continuation`, `tests::goldens::nullary_declared_data_uses_its_bare_name`, `tests::goldens::a_binder_skips_the_names_the_type_mentions`, `tests::goldens::static_operators_spell_as_the_grammar_writes_them`.
- `present_value`: a value at a page width, bounded at `DEPTH_LIMIT`; a flow composite is written infix, `f then g`. Witnesses: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`, `tests::goldens::here_witness_pins_identity_notation`, `tests::goldens::string_controls_stay_in_one_escaped_literal`, `tests::goldens::pair_of_injections_pins_sum_notation`, `tests::goldens::n_ary_tuples_and_injections_spell_between_their_braces`, `tests::goldens::records_spell_their_fields_in_label_order`, `tests::goldens::record_value_breaks_fields_at_the_narrow_page`, `tests::goldens::beyond_the_depth_limit_renders_deep`, `tests::goldens::a_composite_of_flows_spells_infix`.
- `present_computation`: an elaborated body at a page width in its canonical form, every exit the lowering infers elided — a tail returner written as its value, a tail call bare, `pure v` where the body goes on — which the lowering reads back to the same term; a source as written is the formatter's. Read through `CoreSource::restoring` with the `Restoration` of the checker's elaboration, every run the checker inferred is elided too, a computation written where a value is read, while a written `run c` and a written bind print as written. A lazy pair is the positional copattern block `&{.0 => c, .1 => d}`. Witnesses: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`, `core_source::tests::a_restored_elaboration_reads_as_written`.
- `present_computation_line`: the same body on as few lines as it admits, written by the same walk straight into text with no layout document built — the spelling a run's value prints. Witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`.
- `Presentation`, `Fidelity`: the text, and whether it says the whole node, by the nodes met rather than the characters written. Witnesses: `tests::goldens::fidelity_follows_nodes_not_the_characters_of_a_name`, `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`.
- `Source`, `Former`, `Name`: the one question the printer asks of its input; a malformed source — a child of the wrong sort, a dangling node, a cycle — is written `?`, never a panic. Witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`.
- `CoreSource`, `CoreNode`, `Restoration`: the core arena as a source, constants and abstract types named from a table indexed by constant, and an elaboration's rebuilt nodes read as the nodes they were rebuilt from.
- `ContentSource`: an incremental checkpoint's content table as a source, constants and abstract types named by their item keys; an unresolved node, a hole, a mark and an index past the table are written `?`. Witnesses: `content_source::tests::value_ty_covers_every_reachable_former`, `content_source::tests::comp_ty_covers_every_reachable_former`, `content_source::tests::ty_dispatches_on_polarity`, `content_source::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`, `content_source::tests::types_render_without_debug`, `content_source::tests::a_malformed_table_spells_unknown`.
- `DEPTH_LIMIT`, `ValueDepth`: the value depth at which the printer writes `<deep>`.
- `PresentationError`: a layout ceiling reached while building or rendering, or a defect in the walk's own bookkeeping.
- `PageWidth`, re-exported from `gandr-surface-layout`.
- `Form`: `Sugared` or `Explicit`, the spelling every entry point writes. Witnesses: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`, `tests::goldens::the_sugared_form_breaks_its_infix_and_lists_at_the_narrow_page`.

## Expected features

A caller supplies a `Source` whose node handles are `Copy`, the root and a page width. Names of constants and abstract types come from the caller: `CoreSource` takes them as a table indexed by `ConstantIndex`, and a name past the table is written `?`. The layout ceilings are the engine's defaults, which hold a presentation of a million document nodes.

## Examples

Present a dependent function type in both forms, at a wide and a narrow page:

```rust
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::PresentationError;
use gandr_surface_pretty::present_type;

fn main() -> Result<(), PresentationError> {
    let mut core = CoreArena::new();
    let universe = core.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let outer_code = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let outer = core.value_type_element(outer_code, Level::zero());
    let inner_code = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let inner = core.value_type_element(inner_code, Level::zero());
    let returns_inner = core.comp_type_returner(inner);
    let function = core.comp_type_arrow(outer, returns_inner);
    let suspended = core.value_type_thunk(function);
    let applied = core.comp_type_arrow(outer, returns_inner);
    let body = core.comp_type_arrow(suspended, applied);
    let pi_inner = core.comp_type_pi(universe, body);
    let pi_outer = core.comp_type_pi(universe, pi_inner);

    let source = CoreSource::new(&core, &[]);
    let root = CoreNode::CompType(pi_outer);
    let explicit = present_type(&source, root, PageWidth::from(100_u32), Form::Explicit)?;
    assert_eq!(explicit.as_ref(), "(a : Type) -> (b : Type) -> +U (a -> -F b) -> a -> -F b");
    let sugared = present_type(&source, root, PageWidth::from(100_u32), Form::Sugared)?;
    assert_eq!(sugared.as_ref(), "(a : Type) -> (b : Type) -> (a => b) -> a -> -F b");
    let narrow = present_type(&source, root, PageWidth::from(40_u32), Form::Explicit)?;
    assert_eq!(narrow.as_ref(), "(a : Type) -> (b : Type) -> +U (a ->\n  -F b) -> a -> -F b");
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
cargo nextest run -p gandr-surface-pretty
```

The goldens live in `tests/golden/`, one `.narrow.txt` at 40 columns and one `.wide.txt` at 100 per pair; `UPDATE_EXPECT=1` rewrites them.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Two forms of one walk, a body's canonical form with its exits elided, the answers the lint wall checks at compile time, tests and their limits, references | [`src/lib.rs`](src/lib.rs) |
| The input is a source | [`former`](src/former.rs) |
| Products, sums and tuples between their braces, native universe paths, break points, a body's statements breaking together, binder names, bounds | [`walk`](src/walk.rs) |

The deferred golden rows, each with the former it needs, are tracked in [#206](https://github.com/gandr-lang/gandr/issues/206).

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
