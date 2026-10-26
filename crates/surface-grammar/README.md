# gandr-surface-grammar

The checked precedence-bounded grammar of the gandr surface: rules over a precedence DAG, three build-time gates, the mold table a parser reads, the walk index over it, the built-in surface, and the mold highlighter.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Pbg` is a set of `Rule`s, each a `Regex` over tiles and sort holes at one `Sort` and one precedence group, that has passed three gates: Operator Form, Unique Tiles and Assumption 3. Building it assigns every tile occurrence a mold — its position in its rule's form — with precedence bounds, zipper steps, same-form adjacency, form-membership flags and a closing class precomputed, and folds the tables into a `GrammarFingerprint`. `walk_index` instantiates the theory-graphs walk machine over the molds; `comparison_table` reads the operator-precedence relation off it. `built_in` is the gandr surface itself. `RoleTable` is the mold highlighter: one highlight role per mold, and a molded tree's spans read through it. The crate is `no_std` over `core` and `alloc` and depends on `gandr-surface-render-remote`, `gandr-surface-syntax` and `gandr-theory-graphs`.

**Why.** A tile-based parser asks, for every token, which molds its label can take and how two adjacent molds relate. Both answers are fixed once the grammar is, so they are computed once at build and read by index, and the gates refuse at build any grammar for which a parser's local choice would be ambiguous. A parser's tree stores `MoldId`s, which mean something only under the table that numbered them, so the table carries a fingerprint a consumer stores beside them.

**How.** `Pbg::build` checks rule headers, then Operator Form per rule, then numbers every tile occurrence in rule order and left to right while interning its context, refusing a repeated label in one context (Unique Tiles), then checks Assumption 3 over the sorts each form can begin and end with. One fold per rule computes nullability, first and last tiles, adjacency and required-hole edges; the closing class is a sinks-first fold over the rule's tile-graph condensation. Every walk is iterative, and every table is ordered, so a build is the same on every run.

## Provided features

- `Regex`, `RegexView`, `RegexShape`, `Sym`, `Tile`: a form as a flat pre-order arena, built by `empty`, `sort`, `tile`, `seq`, `alt`, `optional` and `repeat` and read back as a tree.
- `Rule`, `Sort`, `Adaptation`, `Pbg::build`, `Pbg::build_table`, `PbgError`: rules checked into a grammar, every refusal typed and checked in a fixed order; `Sort` decodes from a `GroutSort` tag.
- `validate_operator_form`, `validate_unique_tiles`, `validate_assumption_3`: the gates on their own.
- `MoldDef`, `RCtxId`, `RCtxStep`, `StepSym` and the `Pbg` mold queries — `mold`, `bounds`, `step`, `candidates`, `fresh_candidates`, `candidate_counts`, `adjacencies`, `mold_successors`, `molds_adjacent` with `MoldsAdjacent`, `form_first`, `form_last` and the per-mold flags: the mold table a parser reads.
- `Pbg::closing_class`: the bracket family a mold's form completes into.
- `Pbg::least_interchangeable`: the least mold a pushed tile is read exactly as, its label aside.
- `Pbg::tile_kind`, `Pbg::observation`, `Pbg::tile_set` and `Pbg::tile_table_bytes`, with `TileKind`, `Observation`, `TileSet`, `MoldSet`, `MoldWord`, `MoldWordIndex`, `MoldInSet` and `TileTableBytes`: the tile automaton — each mold's kind and observation class, and the molds a parser admits by kind and sort as bitsets, derived once per grammar.
- `Pbg::rule_of` and `Pbg::named_kind`: the rule a mold belongs to and the named kind that rule realises, total over the mold table — what a consumer of a molded tree dispatches on.
- `Pbg::fingerprint`: the grammar's identity, pinned for the built-in surface.
- `walk_index`, `reachable_molds`, `comparison_table`, `seen_key_verdict`, `GrammarWalkSym`, `MAX_WALK_CHAIN_LEN`: the walk machine over a grammar and the relations read off it.
- `built_in`, `built_in_prec_table`, `PrecTable`: the gandr surface and its named precedence groups, the mold table thawed from frozen tables.
- `RoleTable`, `HighlightError`: the role of every mold, read off a grammar, and the highlight spans of a tree molded under it; a tree under another grammar and a tile past the table are refused.
- `named_kind_parity`, `named_kind_realization`, `TREE_SITTER_NAMED_KINDS`, `PBG_ONLY_KINDS`: how every named node kind is realised.
- `SPELLED`, `Spelled`, `Ascii`, `Spelling`, `spelled`, `aliased` and the named entries `EQUIVALENCE`, `FLOW`, `ISOMORPHISM`, `CONS`, `UNRESTRICTED`: every construct has an ASCII spelling and may have a Unicode one; the table pairs each glyph tile with its ASCII token or head, which the labeler molds as the glyph and the printer writes when asked for ASCII. `PRIME` is the identifier prime, which has none. Witnesses: `tests::spelling::every_glyph_tile_of_the_grammar_has_an_ascii_spelling`, `tests::spelling::each_glyph_is_written_in_the_spelling_asked`.

## Expected features

- **A labeler speaking the grammar's labels.** A parser asks for a token's molds by `TileLabel`; a label is a spelling (`(`, `def`, `->`) or a lexeme class (`identifier`, `type_identifier`, `string_fragment`). A token labelled with a label no rule declares has no candidates.
- **Mold ids read under their fingerprint.** A `MoldId` is a position in one grammar's table; a consumer that stores ids stores the `GrammarFingerprint` beside them and refuses ids under a different one.
- **Layout cut by the labeler.** The highlighter reads a tree's layout as the labeler cut it: one node per comment, per shebang line and per run of whitespace, a comment opening with `//` or `/*` and a shebang with `#!`.

## Examples

Build a two-group grammar and read its molds.

```rust
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TileLabel;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let mut spec = PrecSpec::new();
    let atom = spec.insert("atom", Assoc::Non)?;
    let add = spec.insert("add", Assoc::Left)?;
    spec.add_edge(atom, add)?;
    let dag = PrecDag::build(&spec)?;

    let plus = Regex::seq([
        Regex::sort(Sort::Expression),
        Regex::tile(TileLabel("+")),
        Regex::sort(Sort::Expression),
    ]);
    let pbg = Pbg::build(dag.clone(), vec![
        Rule::new(RuleName("plus"), Sort::Expression, add, plus),
        Rule::new(RuleName("x"), Sort::Expression, atom, Regex::tile(TileLabel("x"))),
    ])?;
    assert_eq!(1, pbg.candidates(TileLabel("+")).len());
    assert!(pbg.candidates(TileLabel("-")).is_empty());

    // Two holes side by side fail the Operator Form gate.
    let juxtaposed = Regex::seq([Regex::sort(Sort::Expression), Regex::sort(Sort::Expression)]);
    let refused = Pbg::build(dag, vec![Rule::new(RuleName("app"), Sort::Expression, add, juxtaposed)]);
    assert!(matches!(refused, Err(PbgError::AdjacentSorts { .. })));
    Ok(())
}
```

Run the tests:

```sh
cargo nextest run -p gandr-surface-grammar
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Scope, specification evidence, references | [`src/lib.rs`](src/lib.rs) |
| Regex layout, successor runs and membership flags, lookups, the fingerprint | [`model`](src/model.rs) |
| The gates | [`check`](src/check.rs) |
| Molds, contexts and closing classes | [`mold`](src/mold.rs) |
| Tile kinds, observation classes and tile sets | [`automaton`](src/automaton.rs) |
| The walk index and comparison table | [`walk`](src/walk.rs) |
| The built-in surface and its frozen tables | [`surface`](src/surface.rs) |
| The bridges and the universe | [`surface::type_shell`](src/surface/type_shell.rs) |
| Type operators, the unit value, the splice | [`surface::term`](src/surface/term.rs) |
| The named-kind inventory | [`parity`](src/parity.rs) |
| The highlighter | [`highlight`](src/highlight.rs) |

## References

- `Kovács-2022-staged_compilation_twolevel_type_theorya` — lineage: András Kovács, "Staged Compilation with Two-Level Type Theory", _ICFP_, 2022, `doi:10.1145/3547641` — the splice `~t`.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
