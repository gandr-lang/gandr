# gandr-surface-pretty

The presentation printer: a checked core type or a normal-form value, written in its one surface spelling and laid out at a page width through `gandr-surface-layout`.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The input is a source](#the-input-is-a-source)
- [One spelling per former](#one-spelling-per-former)
- [Break points](#break-points)
- [Binder names](#binder-names)
- [Bounds](#bounds)
- [Tests: the floor and the deferred rows](#tests-the-floor-and-the-deferred-rows)
- [License](#license)

## Synopsis

**What.** `present_type` and `present_value` take a `Source` — a store that answers, for one node, the `Former` it carries — a root and a `PageWidth`, and return a `Presentation`: the laid-out text and its `Fidelity`, which says whether every node was written in full. `CoreSource` reads the core arena; a face with a store of its own implements `Source` beside it. The crate uses `core` and `alloc` under `no_std`.

**Why.** A transcript line, a hover and a diagnostic operand each name a type or show a value, and each must say it the same way, in the syntax a reader can type back. One producer of that spelling, laid out by one engine, keeps every face in agreement on both the words and where a line breaks.

**How.** The walk reads the root's former, spells it or schedules its children, and joins their documents on an explicit task stack. Every break point is a choice between the byte the one-line spelling carries there and a line break, so a page the one-line spelling fits selects it unchanged; the layout engine chooses among the rest by least overflow, then fewest lines. A pre-scan over the same nodes collects the names a type mentions, so a generated binder name never shadows one.

## References

- Sorawee Porncharoenwase, Justin Pombrio, and Emina Torlak. "A Pretty Expressive Printer." _Proceedings of the ACM on Programming Languages_ 7, OOPSLA2, October 2023. [doi:10.1145/3622837](https://doi.org/10.1145/3622837), [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) — the cost order and the computation width the documents here are resolved under.
- Jean-Philippe Bernardy. "A Pretty But Not Greedy Printer (Functional Pearl)." _Proceedings of the ACM on Programming Languages_ 1, ICFP, article 6, September 2017. [doi:10.1145/3110250](https://doi.org/10.1145/3110250) — choosing a layout over all candidates rather than the first that fits, which lets each break point be an independent choice.
- Phillip M. Yelland. "A New Approach to Optimal Code Formatting." Technical report, Google, 2016. [research.google](https://research.google/pubs/a-new-approach-to-optimal-code-formatting/) — formatting as least cost over alternative layouts with an overflow penalty, the tradition the break-point choices belong to.
- Philip Wadler. "A Prettier Printer." In Jeremy Gibbons and Oege de Moor (editors), _The Fun of Programming_, Palgrave Macmillan, 2003. [prettier.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf) — the document algebra the documents are written in.

## Provided features

- `present_type`: a value or computation type at a page width. Witnesses: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`, `goldens::tests::universes_spell_their_sort_and_level`, `goldens::tests::dependent_function_type_breaks_before_codomain`, `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`, `goldens::tests::arrow_chain_breaks_before_each_continuation`, `goldens::tests::nullary_declared_data_uses_its_bare_name`, `goldens::tests::a_binder_skips_the_names_the_type_mentions`.
- `present_value`: a value at a page width, bounded at `DEPTH_LIMIT`. Witnesses: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`, `goldens::tests::string_controls_stay_in_one_escaped_literal`, `goldens::tests::pair_of_injections_pins_sum_notation`, `goldens::tests::record_value_breaks_fields_at_the_narrow_page`, `goldens::tests::beyond_the_depth_limit_renders_deep`.
- `Presentation`, `Fidelity`: the text, and whether it says the whole node, by the nodes met rather than the characters written. Witnesses: `goldens::tests::fidelity_follows_nodes_not_the_characters_of_a_name`, `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`.
- `Source`, `Former`, `Name`: the one question the printer asks of its input; a malformed source — a child of the wrong sort, a dangling node, a cycle — is written `?`, never a panic. Witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`.
- `CoreSource`, `CoreNode`: the core arena as a source, constants and abstract types named from a table indexed by constant.
- `DEPTH_LIMIT`, `ValueDepth`: the value depth at which the printer writes `<deep>`.
- `PresentationError`: a layout ceiling reached while building or rendering, or a defect in the walk's own bookkeeping.
- `PageWidth`, re-exported from `gandr-surface-layout`.

## Expected features

A caller supplies a `Source` whose node handles are `Copy`, the root and a page width. Names of constants and abstract types come from the caller: `CoreSource` takes them as a table indexed by `ConstantIndex`, and a name past the table is written `?`. The layout ceilings are the engine's defaults, which hold a presentation of a million document nodes.

## Examples

Present a dependent function type at a wide and a narrow page:

```rust
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
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
    let wide = present_type(&source, root, PageWidth::from(100_u32))?;
    assert_eq!(wide.as_ref(), "(a : Type) -> (b : Type) -> +U (a -> -F b) -> a -> -F b");
    let narrow = present_type(&source, root, PageWidth::from(40_u32))?;
    assert_eq!(narrow.as_ref(), "(a : Type) -> (b : Type) -> +U (a ->\n  -F b) -> a -> -F b");
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
cargo nextest run -p gandr-surface-pretty
```

The goldens live in `tests/golden/`, one `.narrow.txt` at 40 columns and one `.wide.txt` at 100 per pair; `UPDATE_EXPECT=1` rewrites them.

## The input is a source

The printer asks one question of its input, the former at a node, through the `Source` trait, and reads nothing else. `CoreSource` answers it over the core arena; `gandr-surface-repl` answers it over the incremental checker's content tables, beside the face that holds them, so this crate depends on neither the checkpoint store nor the table format.

- **Alternatives.** Taking the core arena alone would make a face holding content tables mint a core arena first, duplicating the checker's own minting and adding the incremental tier to this crate's dependencies. The prior implementation printed surface types and values that the engine built for it, a tree that cannot be malformed and that no checkpoint holds.
- **Reversal.** A second reader needs more than the former per node — a span, an origin for a binder name — at which point the question widens, or the per-node dispatch shows in a profile.

## One spelling per former

Every former has exactly one spelling, the one the surface grammar parses, so a printed type reads back as the type it names: `Integer`, `String`, `Unit`, `A * B`, `A + B`, `+U C`, `-F A`, `A -> C`, `(x : A) -> C`, `Type`, `Type[-]`, `Type[+, l]`, `Type[-, l]`, an abstract type and a constant by name, and a decode as the code it reads; values are `()`, literals with their canonical digits and escapes, `(a, b)`, `Inl(v)` and `Inr(v)`. Binding strength follows the grammar's bands, tightest first: atoms, the bridges `+U` and `-F` ([the bridges and the universe](../surface-grammar/README.md#the-bridges-and-the-universe-are-built-in-spellings)), product, sum, arrow. Product and sum associate to the right and parenthesize a left operand of equal strength; an arrow's domain is bare up to a sum and its codomain bare.

A node the surface has no spelling for — a lift, the numeric atom, a linear or unbound variable, a term where a type stands — is written `?`, and a thunk value `<thunk>`; each makes the presentation approximate. Fidelity is recorded by the nodes the walk met, so a name that happens to contain `?` stays faithful.

The prior implementation spelled its own surface — `Π(x : A). B`, `→`, `U` and `F` — and parenthesized every arrow, so `Integer → String → F Unit` printed as `(Integer → (String → F Unit))`. Here the spellings are the grammar's, and a right-nested chain is bare because the grammar parses it so: the REPL's corpus witness expects every signature's line to be its source's own text.

- **Alternatives.** Spelling the prior implementation's notation would print text the surface cannot read back. Parenthesizing every compound operand is simpler to state and makes every chain longer than its source.
- **Reversal.** A ruled change to the grammar's spellings or bands; this crate follows it, never leads it.

## Break points

A break point is a choice between the byte the one-line spelling carries there and a line break: after an arrow, an infix symbol and a comma, a space or a break indented two columns; before a bracket's closer, nothing or a break. The broken branch stands first, matching the layout engine's left-biased fallback when both alternatives are width-tainted. Each choice is independent of the others, so the least-cost layout may break inside a parenthesized operand where that alone fits the page: the narrow page of the example above breaks inside `+U (a -> -F b)`.

- **Alternatives.** A group per arrow chain, breaking all of its arrows or none, outer chains before inner, reads as the prior implementation's long dependent arrow did; under the cost order, overflow then line count, it takes more lines than a single inner break, and the engine would choose it only if inner breaks were offered inside the outer group's broken branch alone.
- **Reversal.** A reader rules that a chain breaks whole; the walk then builds chain groups and the goldens move with it.

The computation width is twice the page. Past it the engine resolves without its optimality guarantee: a frontier wins over a tainted promise, and two tainted promises retain the left alternative. At zero columns, both the inline space and the two-column continuation indentation exceed the computation width; the broken separator remains the fallback (`goldens::tests::doubly_tainted_pair_keeps_the_broken_separator`). A wider computation width admits more memoized states; twice the page bounds that work. The choice reverses when a wider computation width improves a presentation at an acceptable cost.

## Binder names

The core is nameless, so a dependent arrow's binder is generated: `a` through `z`, then `a1`, `b1`, and so on, the outermost binder first, skipping every name the type mentions — a constant or an abstract type of that name. The prior implementation printed the binder name its surface type carried.

- **Alternatives.** Printing a de Bruijn index reads as nothing the surface parses; reusing a mentioned name would make the codomain ambiguous.
- **Reversal.** The core carries a binder's source name as an origin hint, and the printer prints it when no mentioned name collides.

## Bounds

Nothing here recurses. The walk drains an explicit task stack; a value deeper than `DEPTH_LIMIT`, 32 value formers, is written as its outer formers around one `<deep>` leaf, as the prior implementation did; and a source is visited at most 65,536 times, so a malformed one — a cycle above all — is written `?` rather than looping. The pre-scan for mentioned names and the walk reach the same nodes, so the scan's budget bounds the walk too. A layout ceiling is a `PresentationError`, never partial output.

## Tests: the floor and the deferred rows

The prior implementation's 16 golden tests are the floor. Eight are here under their names and eight wait for a former the core does not carry yet.

| Floor | Here | Deferred |
| ----- | ---- | -------- |
| 16 | 8 | 8 |

The ported rows take the core's forms. `dependent_function_type_breaks_before_codomain` and `long_dependent_function_type_breaks_at_the_narrow_page` bind universes with generated names where the prior rows bound named values; the small one stays on one line at both pages, as before. `arrow_chain_breaks_before_each_continuation` is the same chain, bare. `record_value_breaks_fields_at_the_narrow_page` carries the prior record's three fields as a right-nested pair, and `nullary_declared_data_uses_its_bare_name` the nullary declared type as an abstract type. `string_controls_stay_in_one_escaped_literal`, `pair_of_injections_pins_sum_notation` and `beyond_the_depth_limit_renders_deep` keep their values, the last with `Inl(…)` where the prior row nested lists.

Deferred, with the former each needs:

| Test | Former |
| ---- | ------ |
| `effectful_returner_keeps_its_suffix_after_the_payload` | an effect row on `-F` |
| `lazy_product_and_thunk_types` | the lazy computation product |
| `stack_type_pins_bracketed_pair_notation` | the stack type |
| `stack_with_arrow_keeps_both_bracketed_items` | the stack type |
| `declared_data_application_breaks_arguments` | declared data with arguments |
| `nested_list_value_stays_grouped` | list values, from declared data |
| `annotations_are_transparent` | an annotated value; no core value carries one |
| `here_witness_pins_identity_notation` | the identity witness |

The crate carries 15 tests: the eight ported rows and seven additional witnesses — every type former's spelling, universes, binder names, every value leaf, malformed sources, fidelity by node, and the doubly-tainted separator at zero columns.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
