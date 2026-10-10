# gandr-surface-pretty

The presentation printer: a checked core type or a normal-form value, written in its one surface spelling and laid out at a page width through `gandr-surface-layout`.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The input is a source](#the-input-is-a-source)
- [One spelling per former](#one-spelling-per-former)
- [Native universe paths](#native-universe-paths)
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

- `present_type`: a value or computation type at a page width. Witnesses: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`, `goldens::tests::universes_spell_their_sort_and_level`, `goldens::tests::dependent_function_type_breaks_before_codomain`, `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`, `goldens::tests::arrow_chain_breaks_before_each_continuation`, `goldens::tests::nullary_declared_data_uses_its_bare_name`, `goldens::tests::a_binder_skips_the_names_the_type_mentions`, `goldens::tests::static_operators_spell_as_the_grammar_writes_them`.
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

- **Alternatives.** Taking the core arena alone would make a face holding content tables mint a core arena first, duplicating the checker's own minting and adding the incremental tier to this crate's dependencies.
- **Reversal.** A second reader needs more than the former per node — a span, an origin for a binder name — at which point the question widens, or the per-node dispatch shows in a profile.

## One spelling per former

Every former has exactly one spelling, the one the surface grammar parses, so a printed type reads back as the type it names: `Integer`, `String`, `Unit`, `A * B`, `A + B`, `+U C`, `-F A`, `A -> C`, `(x : A) -> C`, the static Pi `A -> B` between value types, `Type`, `Type[-]`, `Type[+, l]`, `Type[-, l]`, an abstract type and a constant by name, and a decode as the code it reads; values are `()`, literals with their canonical digits and escapes, `(a, b)`, `Inl(v)`, `Inr(v)`, the static abstraction `\a. v`, and a static application as its spine, `f(a, b)` for `f` applied to `a` and then to `b` ([type operators](../surface-grammar/README.md#type-operators-the-static-abstraction-and-the-value-function-space)). Binding strength follows the grammar's bands, tightest first: atoms, the bridges `+U` and `-F` ([the bridges and the universe](../surface-grammar/README.md#the-bridges-and-the-universe-are-built-in-spellings)), product, sum, arrow. Product and sum associate to the right and parenthesize a left operand of equal strength; an arrow's domain is bare up to a sum and its codomain bare. A static abstraction binds as loosely as an arrow, its body running to the right, and an application is an atom whose operator is parenthesized unless it is one, so a redex reads `(\a. a)(Integer)`. The value-function alias `(A, B) => C` is never printed: it lowers to `+U (A -> B -> -F C)`, and the printer writes what the core holds.

A node the surface has no spelling for — a lift, the numeric atom, a linear or unbound variable, a term where a type stands — is written `?`, and a thunk value `<thunk>`; each makes the presentation approximate. Fidelity is recorded by the nodes the walk met, so a name that happens to contain `?` stays faithful.

A right-nested arrow chain stays bare because the grammar parses it so. The REPL's corpus witness expects each signature's line to be its source's own text.

- **Alternatives.** A notation independent of the grammar would print text the surface cannot read back. Parenthesizing every compound operand is simpler to state but lengthens every chain.
- **Reversal.** A ruled change to the grammar's spellings or bands; this crate follows it, never leads it.

## Native universe paths

The native presentations are `Path_U(a, b)`, `refl(a)`, `equiv(f, g)` and `pathProduct(p, q)`. Endpoint, map and product order is retained. Each is explicitly `Fidelity::Approximate`: these forms have no surface parser syntax, and an equivalence’s display does not include its classifier or replay evidence. The core adapter and checkpoint adapter expose the same value-child positions.

**Choice.** Show the structural constructor instead of an unreadable marker, while withholding a surface round-trip claim. The printer neither compares certified maps nor replays transport. **Reversal.** A faithful notation requires parser and lowering rules that preserve all required information. `native_paths_preserve_ordered_endpoints_and_maps` checks the order and approximation boundary through public presentation.

## Break points

A break point is a choice between the byte the one-line spelling carries there and a line break: after an arrow, an infix symbol and a comma, a space or a break indented two columns; before a bracket's closer, nothing or a break. The broken branch stands first, matching the layout engine's left-biased fallback when both alternatives are width-tainted. Each choice is independent of the others, so the least-cost layout may break inside a parenthesized operand where that alone fits the page: the narrow page of the example above breaks inside `+U (a -> -F b)`.

- **Alternatives.** A group per arrow chain would break all arrows or none, outer chains before inner ones. Under the cost order, overflow then line count, this can take more lines than a single inner break. Independent choices allow that shorter layout.
- **Reversal.** A reader rules that a chain breaks whole; the walk then builds chain groups and the goldens move with it.

The computation width is twice the page, saturating at its maximum. Past it the engine resolves without its optimality guarantee: a frontier wins over a tainted promise, and two tainted promises retain the left alternative. At zero columns, both the inline space and the two-column continuation indentation exceed the computation width; the broken separator remains the fallback (`goldens::tests::doubly_tainted_pair_keeps_the_broken_separator`). A wider computation width admits more memoized states. The choice reverses when a wider computation width improves a presentation at an acceptable cost.

## Binder names

The core is nameless, so a dependent arrow's binder and a static abstraction's are generated: `a` through `z`, then `a1`, `b1`, and so on, the outermost binder first, skipping every constant or abstract-type name encountered by the scan. A new binder is refused when the candidate counter cannot advance; cached names remain available. Name avoidance refers to the scanned view, not an atomic snapshot of a changing source.

- **Alternatives.** Printing a de Bruijn index reads as nothing the surface parses; reusing a mentioned name would make the codomain ambiguous.
- **Reversal.** The core carries a binder's source name as an origin hint, and the printer prints it when no mentioned name collides.

## Bounds

Nothing here recurses. Values stop at `DEPTH_LIMIT`, 32 value formers, with one `<deep>` leaf; static-spine inspection obeys that depth limit too. The naming scan and scheduled document walk each allow at most 65,536 visits. The walk has its own budget because a source may change after the scan; either pass can refuse with `?`, approximate, rather than loop. A late walk refusal can leave unused documents charged to the builder. A layout ceiling returns `PresentationError`, never partial output. Witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`.

## Tests: the floor and the deferred rows

The golden fixtures cover exact grammar spellings and their narrow and wide layouts; [Provided features](#provided-features) names their observers. Boundary witnesses cover truncation across all four core-node families, admission-table endpoints, depth saturation, candidate rounds, binder exhaustion, error causes and layout refusals.

Run `RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-surface-pretty` to execute the predicates as well as the independent assertions. Adequacy blocks state the finite input domains and the mutations each witness distinguishes; they do not claim exhaustive coverage.

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

Executable exemptions remain at opaque observation boundaries: the abstract source reader, child-handle provenance without its source, admission-table correspondence to declarations not held by the adapter, and formatting into an opaque destination. Their source contracts name the missing observer; concrete reader, borrowed-key and error-chain obligations retain executable predicates.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
