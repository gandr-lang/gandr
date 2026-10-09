# gandr-surface-grammar

The checked precedence-bounded grammar of the gandr surface: rules over a precedence DAG, three build-time gates, the mold table a parser reads, the walk index over it, and the built-in surface.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Scope](#scope)
- [Regex layout](#regex-layout)
- [Gates](#gates)
- [Molds and contexts](#molds-and-contexts)
- [Closing class](#closing-class)
- [Walk index and comparison table](#walk-index-and-comparison-table)
- [Built-in surface](#built-in-surface)
- [Named-kind inventory](#named-kind-inventory)
- [Fingerprint](#fingerprint)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `Pbg` is a set of `Rule`s, each a `Regex` over tiles and sort holes at one `Sort` and one precedence group, that has passed three gates: Operator Form, Unique Tiles and Assumption 3. Building it assigns every tile occurrence a mold — its position in its rule's form — with precedence bounds, zipper steps, same-form adjacency, form-membership flags and a closing class precomputed, and folds the tables into a `GrammarFingerprint`. `walk_index` instantiates the theory-graphs walk machine over the molds; `comparison_table` reads the operator-precedence relation off it. `built_in` is the gandr surface itself. The crate is `no_std` over `core` and `alloc` and depends on `gandr-surface-syntax` and `gandr-theory-graphs`.

**Why.** A tile-based parser asks, for every token, which molds its label can take and how two adjacent molds relate. Both answers are fixed once the grammar is, so they are computed once at build and read by index, and the gates refuse at build any grammar for which a parser's local choice would be ambiguous. A parser's tree stores `MoldId`s, which mean something only under the table that numbered them, so the table carries a fingerprint a consumer stores beside them.

**How.** `Pbg::build` checks rule headers, then Operator Form per rule, then numbers every tile occurrence in rule order and left to right while interning its context, refusing a repeated label in one context (Unique Tiles), then checks Assumption 3 over the sorts each form can begin and end with. One fold per rule computes nullability, first and last tiles, adjacency and required-hole edges; the closing class is a sinks-first fold over the rule's tile-graph condensation. Every walk is iterative, and every table is ordered, so a build is the same on every run.

## References

- David Moon, Andrew Blinn, Thomas J. Porter, and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025). `doi:10.1145/3763182`; preprint `arXiv:2508.16848` — the precedence-bounded grammar, the Operator Form, Unique Tiles and Assumption 3 conditions of § 3, molds, the walk vocabulary, and the melder's Reduce of figure 29 that decides which forms an operator may take.
- Nils Anders Danielsson and Ulf Norell. "Parsing Mixfix Operators." In _Implementation and Application of Functional Languages (IFL 2008)_, Lecture Notes in Computer Science 5836, pages 80–99, 2011. `doi:10.1007/978-3-642-24452-0_5` — precedence as a graph of groups that need not be totally ordered, which the built-in surface's bands are.
- Micha Sharir. "A Strong-Connectivity Algorithm and Its Applications in Data Flow Analysis." _Computers & Mathematics with Applications_ 7, 1 (1981), pages 67–72. `doi:10.1016/0898-1221(81)90008-0` — the condensation the closing-class derivation folds over.
- Glenn Fowler, Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd, and Tony Hansen. "The FNV Non-Cryptographic Hash Algorithm." RFC 9923, February 2026. `doi:10.17487/RFC9923` — the accumulator the grammar fingerprint is computed with.

## Provided features

- `Regex`, `RegexView`, `RegexShape`, `Sym`, `Tile`: a form as a flat pre-order arena, built by `empty`, `sort`, `tile`, `seq`, `alt`, `optional` and `repeat` and read back as a tree. Witness: `tests::regex::nested_shapes_read_back_as_built`.
- `Rule`, `Sort`, `Adaptation`, `Pbg::build`, `Pbg::build_table`, `PbgError`: rules checked into a grammar, every refusal typed and checked in a fixed order; `Sort` decodes from a `GroutSort` tag. Witnesses: `tests::pbg::pbg_rejects_invalid_prec_before_later_header_errors`, `tests::pbg::pbg_rejects_duplicate_rule_names_deterministically`, `tests::pbg::pbg_rejects_direct_adjacent_sorts_in_sequence`, `tests::pbg::pbg_rejects_adjacency_exposed_by_nullable_sequence_paths`, `tests::pbg::pbg_accepts_terminal_separators_between_sort_uses`, `tests::pbg::pbg_rejects_invalid_operator_form_even_with_adaptation`, `tests::surface::sort_decode_contract`.
- `validate_operator_form`, `validate_unique_tiles`, `validate_assumption_3`: the gates on their own. Witnesses: `tests::pbg::unique_tiles_contract`, `tests::pbg::pbg_rejects_duplicate_rctx_tile`, `tests::pbg::pbg_accepts_same_label_at_distinct_contexts`, `tests::pbg::assumption_3_contract`.
- `MoldDef`, `RCtxId`, `RCtxStep`, `StepSym` and the `Pbg` mold queries — `mold`, `bounds`, `step`, `candidates`, `fresh_candidates`, `candidate_counts`, `adjacencies`, `form_first`, `form_last` and the per-mold flags: the mold table a parser reads. Witnesses: `tests::walk::mold_lookup_checks_bounds`, `tests::walk::mold_bounds_follow_context_nullability`, `tests::walk::rctx_steps_cross_adjacent_symbols`, `tests::walk::same_form_adjacency_is_the_eq_relation`, `tests::walk::fresh_menus_keep_exactly_the_form_openers`, `tests::walk::form_membership_flags_agree_with_their_lists`, `tests::walk::declared_mold_candidate_inventory_is_exact`, `tests::surface::prefix_formers_keep_required_type_tails_unclosed`, `tests::surface::infix_type_operator_keeps_clean_completion`.
- `Pbg::closing_class`: the bracket family a mold's form completes into. Witnesses: `tests::closing_class::closing_class_is_form_level`, `tests::closing_class::closing_class_repeat_with_exit_shares_its_component_answer`.
- `Pbg::fingerprint`: the grammar's identity, pinned for the built-in surface. Witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`.
- `walk_index`, `reachable_molds`, `comparison_table`, `seen_key_verdict`, `GrammarWalkSym`, `MAX_WALK_CHAIN_LEN`: the walk machine over a grammar and the relations read off it. Witnesses: `tests::walk::walk_index_projects_every_mold_once`, `tests::walk::comparison_table_is_conflict_free`, `tests::walk::comparison_table_coheres_with_precedence`, `tests::walk::seen_key_verdict_is_recorded`, `tests::walk::walk_lengths_respect_the_chain_cap`.
- `built_in`, `built_in_prec_table`, `PrecTable`: the gandr surface and its named precedence groups. Witnesses: `tests::surface::built_in_precedence_bands_are_exact`, `tests::surface::built_in_adaptations_name_their_rules`, `tests::closing_class::built_in_builds_fast_enough_for_process_per_test_suites`, `surface::tests::precedence_helper_failures_preserve_named_context`.
- `named_kind_parity`, `named_kind_realization`, `TREE_SITTER_NAMED_KINDS`, `PBG_ONLY_KINDS`: how every named node kind is realised. Witness: `tests::surface::named_kind_coverage_is_semantic`.

## Expected features

- **A labeler speaking the grammar's labels.** A parser asks for a token's molds by `TileLabel`; a label is a spelling (`(`, `def`, `->`) or a lexeme class (`identifier`, `type_identifier`, `string_fragment`). A token labelled with a label no rule declares has no candidates.
- **Mold ids read under their fingerprint.** A `MoldId` is a position in one grammar's table; a consumer that stores ids stores the `GrammarFingerprint` beside them and refuses ids under a different one.

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

## Scope

The crate holds the grammar and what is computed from it; it parses nothing. A highlighter and its role vocabulary are not here: a role is a renderer's question, and the vocabulary enters with the first renderer that reads it. The contract suite that drives a parser over the built-in surface is not here either: it needs the parser, and it lives with the parser crate. User-declared operators are not in the grammar: the built-in surface's `operator_declaration` rule parses a fixity declaration so the elaborator can decline it by name, and a grammar is never extended at run time. Adding them adds an extension entry point together with its fixity vocabulary.

## Regex layout

A `Regex` is one vector of entries in pre-order, each holding its node and the length of its subtree, so a child is reached by offset and the type holds no pointer to its own type. `view` borrows a subtree and `shape` reads it one level deep; every walk over a form is an explicit work list.

- Alternatives: a recursive enum with boxed children reads more directly, but owns a pointer to its own type, which the workspace lint policy refuses, and its natural walks and its drop recurse.
- Reversal: a consumer that edits forms in place, which this layout turns into a copy.

## Gates

Operator Form refuses a form in which two sort holes can stand side by side on any path, nullable sequences included, so a hole's extent is always delimited by a tile. Unique Tiles refuses two occurrences of one label in one interned context, so a label and a context name exactly one mold. Assumption 3 refuses two distinct sorts `r` and `s` where a form of `r` can begin with `s` and a form of `s` can end with `r`, over every precedence of each. An adaptation records why a rule's shape departs from the named kind it realises; it never relaxes a gate. `Pbg::build` reports the first violation in a fixed order — headers rule by rule, Operator Form rule by rule, Unique Tiles, then Assumption 3 — so a grammar with several faults always names the same one.

`PbgError` keeps a precedence refusal in its own variant: `PrecedenceDag` carries the DAG's own refusal and `PrecedenceCycle` the cycle named group by group, and `InvalidSort` carries the `GroutSort` tag that failed to decode.

## Molds and contexts

A mold is one tile occurrence: its label, its sort, its precedence group, and the interned context it stands in. Ids are assigned in rule order and left to right within a rule. A context records, per side, whether the form's edge faces a sort hole and the steps a zipper crosses to the next symbol; contexts are interned in a `BTreeMap`, so the table is `no_std` and the interning order fixed. A mold's bound on a side is its own group where a hole can face it there, and the root bound otherwise. `candidates` lists every mold of a label; `fresh_candidates` keeps those with no same-form predecessor and those that can open a form, the menu a parser offers where no form is open.

- Alternatives: a hash-map interner needs `std` or a further dependency and a fixed hasher for a stable order.
- Reversal: a measured build in which interning dominates.

## Closing class

A mold's closing class is the bracket family every completion of its form from that mold ends in: `Paren`, `Bracket` or `Brace`, the families `ClosingClass` names in `gandr-surface-syntax`. It is a property of the form, not of the tile, so the same label derives different classes in different rules: a module member's `=` reaches the module's `}`, a definition's `=` completes at `;` and derives nothing. A completion that ends at a tile closing nothing, at a closer of a family the rule never opens, or in disagreement with another completion gives no class.

Each rule's tiles form a graph under adjacency. Every tile in one strongly connected component reaches the same endings, so the derivation condenses the graph once and folds the components sinks first; every occurrence reads its component's answer. The derivation is linear in the rule's tiles and adjacencies, and the built-in surface builds well within the one-second bound its wall-clock test sets.

- Alternatives: a per-tile memo with a visiting set records a tile inside a repeat before the repeat's exit is known and answers wrongly for a repeat with an exit; a search that rescans the rule's adjacency at every step is cubic on the alternation-heavy rules.
- Reversal: a rule shape whose condensation dominates the build.

## Walk index and comparison table

`walk_index` builds a `gandr-theory-graphs` walk machine whose nonterminals are form groups — a sort at a precedence group — and whose stances are molds, with walks capped at `MAX_WALK_CHAIN_LEN` alternations, 64; an over-long walk is a typed refusal. `reachable_molds` lists the molds the index projects per label. `comparison_table` reads the operator-precedence relation between same-sort molds: `≐` relates consecutive tiles of one form and is read off `Pbg::adjacencies`, a grammar fact rather than a walk; `⋖` and `⋗` relate group representatives and are read off the index's `lt` and `gt` faces at the shared sort. The built-in surface's table is conflict-free. `seen_key_verdict` reports whether keying swing closure on sorts alone would change any row.

## Built-in surface

`built_in` is the gandr surface: 21 precedence groups and 19 tighter-than edges, then the term forms, the type-and-shell forms and the circuit forms. The groups form one expression chain, one pattern chain and one type chain whose union, intersection and lazy-product bands are mutually incomparable between the sum and arrow bands; the item group stands apart from all three. Its pinned shape is 2364 molds, 77 labels projected to more than one mold, and the fingerprint `0x6a74_f2ef_1d8a_5c07`; a change to any form, group or edge moves the fingerprint, and the test pinning it states the change.

## Named-kind inventory

`TREE_SITTER_NAMED_KINDS` lists, ascending, the 124 named node kinds of the surface's tree-sitter grammar; `PBG_ONLY_KINDS` lists the kinds only this grammar has, disjoint from them. `named_kind_parity` classifies every listed kind: `source_file` is the file root, realised by the item forms, and every other kind is realised by a rule's provenance or an adaptation's surface form. A kind is never grammar semantics: forms range over tiles and holes only, and the inventory is how coverage of the named kinds is checked.

## Fingerprint

`Pbg::fingerprint` is 64-bit FNV-1a over the frame byte `M`, the precedence DAG's fingerprint, the mold count, each mold as its label, a zero byte, its context, its group and its sort tag, then the context count and each context as its two sort-facing bytes and its two step lists — a list as its length, then each step as `S` and a sort tag or `T`, a label and a zero byte. Words are little-endian and counts 64-bit, so the value is the same on every platform. The accumulator is the shared `Fnv64` of `gandr-theory-graphs`. A fingerprint keys a cache and is no proof of equality.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
