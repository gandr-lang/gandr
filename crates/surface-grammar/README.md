# gandr-surface-grammar

The checked precedence-bounded grammar of the gandr surface: rules over a precedence DAG, three build-time gates, the mold table a parser reads, the walk index over it, the built-in surface, and the mold highlighter.

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
- [The bridges and the universe are built-in spellings](#the-bridges-and-the-universe-are-built-in-spellings)
- [Type operators: the static abstraction and the value function space](#type-operators-the-static-abstraction-and-the-value-function-space)
- [Named-kind inventory](#named-kind-inventory)
- [Highlighter](#highlighter)
- [Fingerprint](#fingerprint)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Pbg` is a set of `Rule`s, each a `Regex` over tiles and sort holes at one `Sort` and one precedence group, that has passed three gates: Operator Form, Unique Tiles and Assumption 3. Building it assigns every tile occurrence a mold — its position in its rule's form — with precedence bounds, zipper steps, same-form adjacency, form-membership flags and a closing class precomputed, and folds the tables into a `GrammarFingerprint`. `walk_index` instantiates the theory-graphs walk machine over the molds; `comparison_table` reads the operator-precedence relation off it. `built_in` is the gandr surface itself. `RoleTable` is the mold highlighter: one highlight role per mold, and a molded tree's spans read through it. The crate is `no_std` over `core` and `alloc` and depends on `gandr-surface-render-remote`, `gandr-surface-syntax` and `gandr-theory-graphs`.

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
- `Pbg::rule_of` and `Pbg::named_kind`: the rule a mold belongs to and the named kind that rule realises, total over the mold table — what a consumer of a molded tree dispatches on. Witness: `tests::surface::every_mold_resolves_to_its_rule_and_named_kind`.
- `Pbg::fingerprint`: the grammar's identity, pinned for the built-in surface. Witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`.
- `walk_index`, `reachable_molds`, `comparison_table`, `seen_key_verdict`, `GrammarWalkSym`, `MAX_WALK_CHAIN_LEN`: the walk machine over a grammar and the relations read off it. Witnesses: `tests::walk::walk_index_projects_every_mold_once`, `tests::walk::comparison_table_is_conflict_free`, `tests::walk::comparison_table_coheres_with_precedence`, `tests::walk::seen_key_verdict_is_recorded`, `tests::walk::walk_lengths_respect_the_chain_cap`.
- `built_in`, `built_in_prec_table`, `PrecTable`: the gandr surface and its named precedence groups. Witnesses: `tests::surface::built_in_precedence_bands_are_exact`, `tests::surface::built_in_adaptations_name_their_rules`, `tests::closing_class::built_in_builds_fast_enough_for_process_per_test_suites`, `surface::tests::precedence_helper_failures_preserve_named_context`.
- `RoleTable`, `HighlightError`: the role of every mold, read off a grammar, and the highlight spans of a tree molded under it; a tree under another grammar and a tile past the table are refused. Witnesses: `tests::highlight::every_mold_has_a_role`, `tests::highlight::corpus_roles_match_the_golden`, `tests::highlight::spans_partition_the_tile_bytes`, `tests::highlight::layout_takes_a_role_only_as_a_comment_or_a_shebang`, `tests::highlight::a_tree_under_another_grammar_is_refused`, `tests::highlight::a_tile_past_the_table_is_refused`, `highlight::tests::mold_provenance_alignment`, `highlight::tests::role_of_pins_context_free_classes`.
- `named_kind_parity`, `named_kind_realization`, `TREE_SITTER_NAMED_KINDS`, `PBG_ONLY_KINDS`: how every named node kind is realised. Witness: `tests::surface::named_kind_coverage_is_semantic`.

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

## Scope

The crate holds the grammar and what is computed from it; it parses nothing. The highlighter is here because a role is read off the mold table alone; the role vocabulary is not, since every renderer reads it, and it lives in the renderer seam, `gandr-surface-render-remote`. The contract suite that drives a parser over the built-in surface is not here either: it needs the parser, and it lives with the parser crate; the highlighter's corpus suite runs the parser as a dev-dependency. User-declared operators are not in the grammar: the built-in surface's `operator_declaration` rule parses a fixity declaration so the elaborator can decline it by name, and a grammar is never extended at run time. Adding them adds an extension entry point together with its fixity vocabulary.

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

`built_in` is the gandr surface: 21 precedence groups and 19 tighter-than edges, then the term forms, the type-and-shell forms and the circuit forms. The groups form one expression chain, one pattern chain and one type chain whose union, intersection and lazy-product bands are mutually incomparable between the sum and arrow bands; the item group stands apart from all three. Its pinned shape is 2378 molds, 77 labels projected to more than one mold, and the fingerprint `0xf9c2_15a1_2bea_b69c`; a change to any form, group or edge moves the fingerprint, and the test pinning it states the change.

## The bridges and the universe are built-in spellings

The shifts between the value and the computation sorts, Levy's `U` and `F`, are spelled `+U` and `-F`: the sign names the sort the bridge produces, so the suspension `+U C` is a value type, positive, and the returner `-F A` a computation type, negative. Each is one compound tile, which the labeler forms only when the letter ends there: `+Unit` stays the sign before the word `Unit`, and `A + B` is the sum however it is spaced. A type has no unary sign, so the compound tile takes no reading from the sum; `A +U B` reads as a bridge after an operand, which the lowering refuses. The bare letters `U` and `F` are ordinary type names. The universe is the reserved word `Type`, with an optional bracket naming its sort by the same signs and, after a comma, its level: `Type`, `Type[-]`, `Type[+, 1]`. The rules keep the kinds `u_type` and `f_type`, the names the tree-sitter grammar gives the two formers, and `universe_type` joins the kinds only this grammar has.

- Alternatives: keeping `U` and `F` as aliases beside the new spellings, which reserves two capital letters from every program and leaves two spellings for one former; a run-time notation through which a library declares the spellings, which needs user-declared notation the surface does not have.
- Reversal: once user-declared notation is admitted, these spellings move into the prelude that declares them.

The respelling moved the pinned shape from 2364 molds and the fingerprint `0x6a74_f2ef_1d8a_5c07`: the two formers' keyword tiles became the compound tiles, and the universe rule added seven molds.

## Type operators: the static abstraction and the value function space

A type operator is written `\A. T`: the backslash, one binder — a type name or a type variable — a dot and the body, which runs as far right as a `forall`'s does, so `\T. \A. \B. T(A) * B` nests three binders. The labeler reads a backslash in code as one tile; escape sequences stay inside strings and characters, where their scanners read them. Applying an operator reuses `type_application`, `T(A, B)`, whose head is a type name or a type variable: a declaration is named by a lowercase identifier, which molds as a type variable in type position, so an operator declared by `def` applies as `raw_rel_monad(T, A, B)`. Admitting the variable head added one mold and moved the fingerprint from `0x8feb_efc4_2bd0_36d1`.

- Alternatives: a keyword lead such as `fn` at the type sort, which ties with the term lambda wherever a definition's body stands, where a type-only lead molds unopposed; a binder list `\A B. T`, which saves a few backslashes and adds a repetition the lowering would curry anyway.
- Reversal: a binder that needs its classifier written beside it (`\(T : Type -> Type[-]). …`) would take the parenthesized binder as a second alternative of the same rule.

The value function space `A => B` is the alias of the thunked arrow `+U (A -> -F B)`, and `(A, B) => C` its n-ary form, `+U (A -> B -> -F C)`. It is an infix rule in the arrow's group, so the two arrows nest to the right of one another; its n-ary domain is a parenthesized type list, which is why `parenthesized_type` holds one type or several. One rule keeps `(` at a single type-sort mold, so the molder never opens a lookahead window to tell a parenthesized type from a domain list, and the lowering refuses a list anywhere but before `=>`. A case arm's `=>` follows a pattern and this one a type; the two never compete for one slot. Nothing distinguishes the alias from its unfolding after lowering except the printer, which may choose either spelling.

- Alternatives: a separate rule for the n-ary domain, `( T , T+ ) => T`, which gives `(` two type-sort molds tied on the molder's local key; a nullary `() => B` for `+U (-F B)`, which the recorded design does not rule and the surface does not need while `+U (-F B)` is short.
- Reversal: if a tuple type ever takes the parenthesized list, the domain list moves into the alias rule and the tie is settled there.

## Named-kind inventory

`TREE_SITTER_NAMED_KINDS` lists, ascending, the 124 named node kinds of the surface's tree-sitter grammar; `PBG_ONLY_KINDS` lists the kinds only this grammar has, disjoint from them. `named_kind_parity` classifies every listed kind: `source_file` is the file root, realised by the item forms, and every other kind is realised by a rule's provenance or an adaptation's surface form. A kind is never grammar semantics: forms range over tiles and holes only, and the inventory is how coverage of the named kinds is checked.

A molded syntax tree names each form and tile by its `MoldId`; `Pbg::named_kind` reads the kind back as the provenance of the rule the mold was numbered for. The table records each mold's rule as it numbers the molds, so the lookup is total over the table and refuses only an id past it, as `Pbg::mold` does. The record is not folded into the fingerprint, which keys the mold table a parser reads: two grammars with one mold table and different rule provenance share a fingerprint, so a consumer reads kinds from the grammar it holds, after checking the tree's fingerprint against it. Reversal: fold each mold's provenance into the fingerprint once a consumer keys stored kinds by fingerprint alone.

## Highlighter

`RoleTable::build` reads one `HlRole` per mold off a grammar, and `RoleTable::highlight` reads a molded tree's tiles through it into `HlSpan`s over `ByteRange`, the renderer seam's vocabulary. A mold is a tile occurrence's zipper into its form, so a role is a function of the mold alone: its label, the named kind of its rule, the symbols its form places beside it, and the bracket of its form it stands inside. Every role is decided once, at build, and a span costs one table read. A tree molded under another grammar is refused with both fingerprints, and a tile past the table with its id; like `Pbg::named_kind`, the table reads rule provenance the fingerprint does not fold, so it is read under the grammar it was built from.

The classification, in order:

- The comment and shebang rules' tiles are `Comment` and `Directive`; every tile of a shell list separator or a redirection is `Operator`.
- Literals, string pieces, escapes, constructors, type names, type variables, hole names, shell variables, environment assignments and shell words take their class by label; keywords, operators and primitive types take theirs by spelling.
- A label several rules share is told apart by its rule or its neighbours: `?` is a `Hole`, the gradual type or a receive; `!` is part of `fork!` and an operator elsewhere; `+` and `-` are keywords, the sort literals, inside a universe's bracket and operators elsewhere; `_` is a parameter inside a parenthesised list and a variable elsewhere.
- An `identifier` takes the role of its place: a definition after `def`, `rec`, `op`, `oper`, `rule` or `data`; a binding after `as`, `for`, `leta`, `unpack`, `module`, `node` or `feed`; a parameter inside a parenthesised list or an implicit `@[…]` binder; a member after `.`, inside a record `#{…}` or a block of fields; a label for a world, a session branch or a `select`'s label; a call for the operation a circuit node applies; a number for a grade in `+U[…]` and `thunk[…]`; an attribute or decoration name is `Other`.
- Every other tile — a bracket, a separator, a delimiter — is `Other`.

Layout has no mold: a layout node opening with `//` or `/*` is a `Comment`, one opening with `#!` a `Directive`, and whitespace, grout and a minted close take no span. Every tile is one span, and adjacent spans of one role stay two. The enclosing bracket is read by one walk over the rules' forms in mold-id order, the order the mold table numbers them, with the open brackets of the current form on a stack: an opener pushes, a closer pops, and each branch of an alternative starts from the brackets open before it. The walk is checked against the mold table occurrence by occurrence.

Every mold of the built-in surface has a role, 2371 of 2371. Four places the grammar does not tell apart take a coarse role, which a semantic overlay refines: a definition's name is a `FunctionDef` whether it names a function or a value; the head of an application `f(x)` is an expression atom, so a `Variable`; a shell command's head and its arguments are one `shell_word` class, so all `Path`; and the first field of a record expression `#{ x = 1, … }` is an expression atom where later fields are `Member`s.

- Alternatives: a table keyed by a token's lexeme class, which cannot tell a definition's name from a reference, or `?` the hole from `?` the receive, since each pair is one label; tree-sitter highlight queries over the surface's tree-sitter grammar, which keep a second parser and its query files in step with this grammar by hand and cannot read the molded tree the pipeline holds.
- Reversal: a role that depends on more than the mold — a name's resolved kind, a binding's uses — belongs to a semantic overlay over these spans; the classification leaves the grammar when the grammar stops determining it, as user-declared operators would make an operator's spelling a run-time fact. Punctuation is `Other`; a renderer that styles it apart adds a role to the seam.

Consumers: the language server's semantic tokens, the REPL's echoed input and the terminal renderer's paint read these spans, each mapping a role to its own style.

The role golden under `tests/highlight/` mirrors the corpus: one `.roles` file per source, both roots and the pending set, with a line per span — `start..end Role "text"` — and `unexercised.roles`, which names every mold no corpus tile exercises with its role, rule and neighbours, so every mold's role stands in a reviewed line. A source added to the corpus, moved between roots or removed moves its golden with it: `UPDATE_EXPECT=1 cargo nextest run -p gandr-surface-grammar` rewrites the goldens and deletes those whose source is gone, and without it a missing, stale or orphaned golden fails the suite.

- Choice: `expect-test` compares and rewrites the goldens, a file compared whole with a diff on mismatch.
- Alternatives: `insta`, whose review tool and snapshot metadata this suite does not need and whose dependency tree is several times larger; a hand-written comparison, which reports no diff.
- Reversal: a golden that needs redaction or per-snapshot metadata.

## Fingerprint

`Pbg::fingerprint` is 64-bit FNV-1a over the frame byte `M`, the precedence DAG's fingerprint, the mold count, each mold as its label, a zero byte, its context, its group and its sort tag, then the context count and each context as its two sort-facing bytes and its two step lists — a list as its length, then each step as `S` and a sort tag or `T`, a label and a zero byte. Words are little-endian and counts 64-bit, so the value is the same on every platform. The accumulator is the shared `Fnv64` of `gandr-theory-graphs`. A fingerprint keys a cache and is no proof of equality.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
