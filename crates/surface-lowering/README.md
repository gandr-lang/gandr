# gandr-surface-lowering

Lowering the gandr surface into the core language: the molded syntax tree the parser builds in, call-by-push-value core terms, their origins and the module's attribute table out, or a located refusal that says why a form has no core reading.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dispatch on the grammar's named kinds](#dispatch-on-the-grammars-named-kinds)
- [Repairs are refused where they stand](#repairs-are-refused-where-they-stand)
- [Names resolve through tables with no fallthrough](#names-resolve-through-tables-with-no-fallthrough)
- [A module is collected by name and resolved by position](#a-module-is-collected-by-name-and-resolved-by-position)
- [The namespace engine](#the-namespace-engine)
- [Imports bind an alias and resolve nothing](#imports-bind-an-alias-and-resolve-nothing)
- [A form's sort is decided by its own form](#a-forms-sort-is-decided-by-its-own-form)
- [A function tail is a thunked chain of lambdas](#a-function-tail-is-a-thunked-chain-of-lambdas)
- [A block binds each statement over the next](#a-block-binds-each-statement-over-the-next)
- [Three insertions, by the sort of the position](#three-insertions-by-the-sort-of-the-position)
- [Four ways out of the fragment](#four-ways-out-of-the-fragment)
- [Literals mean their decoded value](#literals-mean-their-decoded-value)
- [One refusal per declaration](#one-refusal-per-declaration)
- [The failure classifier](#the-failure-classifier)
- [Attributes: a closed registry and a side table](#attributes-a-closed-registry-and-a-side-table)
- [Origins for terms and types](#origins-for-terms-and-types)
- [Two sweeps, no recursion, one allowance](#two-sweeps-no-recursion-one-allowance)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `lower_module` reads a `gandr-surface-syntax` tree molded under a `gandr-surface-grammar` grammar and mints its declarations into a `gandr-core-term` arena. Each declared name becomes one `LoweredDeclaration` carrying its admission position, the content identity of its signature and definition forms, an origin token, and a `DeclarationOutcome`: a completed signature and definition, an uncompleted signature, a bodiless definition, or the declaration's `LoweringRefusal`. The module's attributes are resolved against a closed `AttributeRegistry` into an `AttributeTable` keyed by declaration content identity, and every minted core node's syntax origin is recorded in an `OriginTable`. Imports are kept and their aliases bound by the `namespace` engine, and every declared name is declared over an outermost `Recognition` scope. `FailureClass` sorts every refusal into the class a consumer acts on.

**Why.** A checker reads core terms, a diagnostic reads source spans, and an obligation ledger reads which declarations are still owed. The lowering is the one place all three are decided together: what the source means in the core fragment, where each core node came from, and whether a declaration that failed to lower failed because the author erred, because the fragment cannot represent it, or because the engine was misused — so no failure the engine refuses is mistaken for an obligation the author owes.

**How.** Every node is dispatched on the named kind the grammar resolves its mold to (`Pbg::named_kind`), and a form's children are split into its own tiles — the tiles of its own grammar rule, read by label — and the forms standing in its holes. A collection pass pairs each name's signature and definition and records which declaration owns every node. An ascending sweep over the level-order arena fixes each node's sort and binder frame from its parent, resolves names and literals, and decides every refusal; a descending sweep then mints each planned node over its already-minted children. Neither sweep recurses, and both spend one caller-set `LoweringBudget`.

## References

- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17> — the value and computation sorts, thunks and returners (`U` and `F`), and the arrow as a computation type, which fix every sort a position demands.
- N. G. de Bruijn. "Lambda calculus notation with nameless dummies." _Indagationes Mathematicae_ 75(5) (1972). <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a lambda's parameter lowers to.
- David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (2025). <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout and the minted closing tiles a repaired tree carries, which the lowering reads and refuses.
- V. I. Levenshtein. "Binary codes capable of correcting deletions, insertions, and reversals." _Soviet Physics Doklady_ 10(8) (1966) — the edit distance that bounds an unknown attribute's suggestion.
- RedPRL. _yuujinchou_ 5.2.0. <https://github.com/RedPRL/yuujinchou> — the namespace design: tries of hierarchical names, the modifier language, the not-found, shadow and hook events a handler settles, and scopes with sections.

## Provided features

- `lower_module`, `LoweringBudget` and `Fuel`: the whole surface-to-core step under one allowance. Witnesses: `lower::tests::a_completed_declaration_lowers_both_halves`, `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`, `lower::tests::force_and_application_lower_over_their_children`, `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`, `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`, `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`, `lower::tests::a_block_binds_each_statement_over_the_next`, `lower::tests::a_call_applies_its_arguments_left_to_right`, `lower::tests::a_refused_declaration_leaves_the_others_lowered`, `lower::tests::a_module_past_the_allowance_is_refused`.
- `LoweredModule`, `LoweredDeclaration`, `DeclarationOutcome` and `DeclarationCount`: one declaration per name, in admission order. Witnesses: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`, `lower::tests::a_bodiless_definition_lowers_its_body_alone`, `module::tests::a_signature_pairs_with_its_definition`, `module::tests::a_definition_pairs_with_a_later_signature`.
- `type_atom`, `type_former`, `TypeAtom`, `TypeFormer`, `HeadArity` and `OperandCount`: the type-head tables by arity. Witnesses: `resolve::tests::every_nullary_type_head_answers_its_atom`, `resolve::tests::every_unary_type_head_answers_its_former`, `lower::tests::an_applied_head_no_former_answers_is_refused`.
- `Scope`, `ScopeId`, `Frame` and `SurfaceName`: the flat binder chain term names resolve through. Witnesses: `resolve::tests::an_inner_binder_shadows_an_outer_one`, `resolve::tests::sibling_extensions_of_one_scope_are_independent`, `resolve::tests::a_chain_walk_past_the_allowance_is_refused`.
- `former_of`, `Former`, `FormName` and `Repair`: the named-kind dispatch and the names a diagnostic writes forms as. Witnesses: `form::tests::every_dispatched_kind_is_pinned`, `form::tests::a_kind_outside_the_table_is_unadmitted`, `form::tests::every_form_name_is_realised_by_the_grammar`.
- `LoweringRefusal`, `FragmentSort`, `FragmentBoundary` and `FormFault`: every refusal, located. Witnesses: one `lower::tests` or `module::tests` witness per variant, each asserting the exact variant, span and class — `lower::tests::forms_outside_the_fragment_are_unadmitted`, `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`, `lower::tests::a_repaired_declaration_is_refused`, `lower::tests::a_juxtaposed_operand_is_refused`, `lower::tests::a_tile_out_of_place_is_refused`, `lower::tests::a_tree_of_another_grammar_is_refused`, `lower::tests::a_mold_the_grammar_does_not_hold_is_refused` among them.
- `LoweringRefusal::classify` and `FailureClass`, the latter re-exported from `gandr-core-term`, which every producer of refusals in the core pipeline classifies into: the classifier. Witnesses: `classify::tests::every_refusal_carries_its_pinned_class`, `classify::tests::the_absence_class_has_no_inhabitant`.
- `AttributeRegistry`, `AttributeSchema`, `RegisteredAttribute`, `EditDistance`, `PayloadForm`, `PayloadVerdict`, `payload_form`, `payload_verdict`, `AttributeEntry`, `AttributeTable` and `AttributedCount`: the closed registry, its five diagnostics and the side table, filed for refused declarations too. Witnesses: `attribute::tests::every_registered_attribute_answers_its_schema`, `attribute::tests::a_near_misspelling_suggests_its_attribute`, `attribute::tests::the_payload_verdict_table_is_pinned`, `lower::tests::an_attribute_is_filed_under_its_declaration_digest`, `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`, `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`.
- `Origin`, `OriginTable`, `OriginToken` and `OriginCount`: the origin of every minted node and every declaration. Witnesses: `origin::tests::each_family_answers_its_own_recorded_origins`, `lower::tests::every_minted_node_has_an_origin`, `lower::tests::a_grouping_lowers_to_what_it_wraps`.
- `Provenance` and `Insertion`: whether a minted node was written by the author or inserted by the lowering, and which bridge an insertion is. Witnesses: `lower::tests::a_value_head_is_forced_and_marked_inserted`, `lower::tests::an_author_written_force_is_not_marked_inserted`, `lower::tests::a_positive_result_gains_a_returner_once`, `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`.
- `namespace`: `Trie`, `Modifier`, `Scope`, the events and their handlers, and `Recognition` with its ordered `SeedTable`s and `ShadowPolicy`. Witnesses: `namespace::namespace::a_deep_patch_merges_instead_of_capturing`, `namespace::namespace::a_sections_closing_modifier_chooses_what_it_passes_on`, `namespace::namespace::every_namespace_walk_is_iterative`, `recognition::recognition::a_path_is_governed_by_its_deepest_resolved_prefix`, `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`.
- `ImportDeclaration`, `ImportIndex`, `ImportUri` and `ModuleImports`: imports kept in source order with their aliases bound. Witnesses: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`, `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`.

## Expected features

- **The grammar the tree was molded under.** `lower_module` takes the `Pbg` whose fingerprint the tree records; a tree of another grammar is refused before any mold is read.
- **A tree from the parser.** Any `SyntaxTree` is admissible, a repaired one included; the lowering refuses what the parser repaired rather than assuming a clean parse.
- **The source outlives the result.** A `LoweredModule` borrows the declared names from the source text the tree spans.
- **One arena per lowering.** Every id in a `LoweredModule` is read against the `CoreArena` that lowering wrote into.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Examples

```rust
use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

fn main() -> Result<(), Box<dyn core::error::Error>> {
    let pbg = built_in()?;
    let tree = parse(&pbg, SourceText::from("def x : Integer ; def x = 3 ;"))?.into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(&pbg, &tree, &mut arena, LoweringBudget::DEFAULT, Recognition::default())?;

    let [declaration] = module.declarations() else {
        unreachable!("one name is declared");
    };
    assert!(matches!(declaration.outcome(), DeclarationOutcome::Completed { .. }));
    Ok(())
}
```

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-lowering` runs the crate's tests; every fragment row a witness exercises is parsed from source by `gandr-surface-parser` and lowered in the same test, and a hand-built tree is used only for a shape the parser never emits.

## Dispatch on the grammar's named kinds

The lowering reads the molded tree directly. A node's form is the named kind the grammar resolves its mold to, and a fixed table (`former_of`) pairs the kinds the fragment reads with the former each is read as; every other kind is unadmitted. A form's own tiles are the child tiles whose mold belongs to the form's own grammar rule, matched by label, and every other written child is an operand. A variant the grammar folds into one form — the unit `()`, a grouping, the reserved pair and the annotation into the parenthesised expression; the signature, definition and function tails into the declaration; a block into the thunk, lambda or function tail that opens it, and each statement into its block by the keyword that opens it — is told apart by its own tiles and named in a diagnostic by its folded kind (`FormName`).

The alternative was an adapter that rebuilds the molded tree into a tree of the lowering's own node kinds and lowers that. It was declined because the adapter is a second vocabulary of forms that drifts from the grammar, and because the grammar already names every form and every tile. Reversal: if one lowering must read trees from grammars whose named kinds differ, the dispatch table is chosen per grammar; an adapter tree still is not.

## Repairs are refused where they stand

The parser completes every input, so a tree can hold grout where the source wrote no term and closing tiles the source never wrote. The first repair among a form's children refuses the form as `MalformedForm` with the `Repaired` fault, at the repair's own span. A hole holding no operand, a hole holding a juxtaposition, and a tile out of its place are refused the same way, as `MissingOperand`, `ExtraOperand` and `MisplacedTile`.

The alternative was to lower around a repair, reading grout as a hole term. It was declined because the core fragment has no hole, and a hole would be an obligation the classifier forbids a refusal to become. Reversal: when the core gains typed holes, grout lowers to one and the repair stops refusing.

## Names resolve through tables with no fallthrough

A type head answers from a table indexed by how it was written: bare, `Unit`, `Integer` and `String`; applied to one argument, `+U` and `-F`. A head no table answers is `UnresolvedTypeHead` carrying the arity it was written with, and a head applied to several arguments reports how many. A term name answers from the binders enclosing it, innermost first, and then from the declarations strictly earlier in admission order; nothing answers otherwise. The unit value is spelled `()`; an identifier spelled `unit` is an ordinary name.

The alternative was a primitive term table answering `unit`. It was dropped because the grammar spells the unit value `()`, so a second spelling would shadow a name the author can declare. Reversal: a primitive term the grammar has no syntax for joins a term table consulted after the binders.

## A module is collected by name and resolved by position

A signature pairs with its definition wherever the two sit in the module, so the signature-then-definition form stays spellable; a second signature or definition for one name is refused naming the first. References resolve by admission position — the position of the declaration that introduced the name — so a declaration's own body and every later declaration are out of its scope, and self-reference and mutual reference are refused as unresolved names. A module whose own shape is wrong — a root that is not a module, a root child that is neither a declaration nor an import, a declaration with no name, an import out of shape, two imports of one alias, an attribute block decorating nothing — refuses the whole run, because nothing can be filed without the name.

## The namespace engine

`namespace` follows yuujinchou: a trie from hierarchical names to bindings held in one arena, a modifier language that rewrites one, the not-found, shadow and hook events a handler settles, scopes with sections, and `Recognition`, the outermost scope lowering declares names over. Its own page, [docs/namespace.md](docs/namespace.md), states [namespaces, modifiers and scopes](docs/namespace.md#namespaces-modifiers-and-scopes), [the arena trie and its walks](docs/namespace.md#an-arena-trie-and-no-recursion), [the outermost scope](docs/namespace.md#the-outermost-scope), and the [tests held](docs/namespace.md#held-tests) until their readers exist.

The alternatives were a crate of its own and the dispatcher. It sits here because the lowering is its one reader: imports and outermost names are decided during lowering. Reversal: a second reader of scope state outside lowering, a session or a language server, moves it to its own crate.

## Imports bind an alias and resolve nothing

`import "URI" as name ;` is kept in source order as an `ImportDeclaration` — the address with its escapes decoded, the alias, the bytes — and its alias bound in the module's import scope: the import's one root binding, its position, run through `alias_as` (`renaming . name`) and imported, so the visible namespace answers each alias and the export stays empty. The import policy refuses every shadow, so a second import of one alias refuses the module as `DuplicateImportAlias`, naming the first; an import out of shape, a missing alias included, is `MalformedForm`. No address is resolved and an alias is not a term name. Reversal: when module resolution lands, the address resolves to an export namespace and the import runs its modifier over that instead of a root binding.

An import without an alias and a second import of one alias were once noted as holes, with the lowering going on past them. Here both refuse, because the module's import scope cannot be filed with an alias missing or bound twice, and their tests say so: `source_import_without_alias_becomes_a_refusal` and `duplicate_source_import_alias_becomes_a_refusal`.

## A form's sort is decided by its own form

The sort a position demands flows down from its parent, and the sort a form produces is a function of the form alone: `+U C` is a value type, `-F A` and `A -> C` are computation types, a thunk, a name, a number, a string and `()` are values, a returner, a force, a lambda, an application and a block are computations, and a grouping is whatever it wraps. A mismatch is therefore refused where the form stands, carrying the sort its position demanded, except at the three positions [the insertions](#three-insertions-by-the-sort-of-the-position) name.

A form is checked in one order, and the first check it fails is its refusal: a kind the fragment has no reading for; a repair among its children; a term where a type belongs or the reverse; a reserved form; a former that does not produce the demanded sort; a variant the fragment does not admit, or an operand count it does not take; and last, the names and literals it holds.

## A function tail is a thunked chain of lambdas

`def f(x: A, y: B) -> R { … }` is one form that writes both halves of a declaration: the declared type `+U (A -> B -> R)` and the definition `thunk (λx. λy. …)`, the block lowered under one binder per parameter. An empty parameter list declares `+U R` and defines `thunk …`. The tail is signed when every parameter states its type and the tail states its result; a tail missing any of them writes its definition alone, so the declaration is a bodiless definition whose thunk the checker cannot synthesise, refused there as `NotSynthesisable` and never by the lowering. The declared `+U` takes the declaration's origin and each arrow its parameter's binder, all written; each lambda takes its binder too.

A call `f(a, b)` is `f` applied to `a`, then to `b`, curried left to right at the call's origin; `f()` is its head alone. Since a signed tail files one form under both halves, its attributes are filed once, under that form's identity.

The alternative was keeping the function tail out of the fragment until a desugaring pass rewrites it into a `def` with a thunk of lambdas, which would put a second tree between the grammar and the lowering. Reversal: when the tail grows a form whose meaning is not a chain of lambdas — an implicit telescope, a recursive definition — that form is lowered by its own plan, and the chain stays the reading of the explicit parameters.

## A block binds each statement over the next

A block is a sequence of `run x <- c;` statements and a last computation. It lowers to a chain of binds, `c₁` bound over the rest of the block with `x` in scope, the last computation innermost, each bind at the origin of its `run` keyword. A block with no last computation is refused at the block as `Arity` with zero; every other statement — `let`, `unpack`, `leta`, `recv`, `acquire`, `release`, `fork` and a bare expression statement — is refused as `Unadmitted`, named by its form, at its keyword or, for an expression statement, at the expression; and a `run` binder that is annotated or is a pattern other than a name is refused the same way, at the annotation or the pattern.

The alternative was lowering `let x = v;` beside `run`, as the substitution of a value. It was declined because the core has no let and the substitution would duplicate `v` at each occurrence, which the fragment has no sharing to undo. Reversal: when the core gains a let, or the lowering gains sharing, `let` lowers to it.

## Three insertions, by the sort of the position

Three positions bridge the sorts instead of refusing a mismatch: a value standing as an application's head is forced, because a force is the only way from a value to a computation; a value type standing as a function's result gains a returner, so `-> Integer` and `-> -F Integer` mean the same and the returner is never doubled; and a function's body, a computation where the declaration takes a value, is thunked. Each bridge is decided by the position's sort and the written form's, both read off the syntax, so no type is consulted. The inserted node takes the origin of the syntax node that demanded it, marked `Provenance::Inserted` with its `Insertion`, so a reader can be shown the cast the author did not write; the checker judges it like any other node, and the kernel re-derives it on readmission.

The recorded design places these insertions in an elaborator that reads the types in hand. This fragment has no elaborator, and its checker returns verdicts rather than terms, so an insertion there would need an elaborated body the readmission does not read; the lowering already knows every position's sort and every form's, so it writes them. The recorded design also thunks a computation in any value position; here only the function body is, and a lambda written where a value belongs stays the `WrongSort` refusal the fragment's suites pin, because the boundary this change moves is the function form's. Alternatives: type-directed insertion in the checker, returning the elaborated body; and inserting at every mismatched position. Reversal: a position whose sort is not read off the syntax — a head whose classifier only normalisation computes — moves the insertion into the checker; and the unit that moves the computation-in-value boundary thunks there too.

## Four ways out of the fragment

`OutOfFragment` names the boundary a form crossed. `Reserved`: the form parses and is declined by name — the product type and the pair — so the classifier's unrepresentable class is inhabited by design. `Unadmitted`: the grammar reads the form and this fragment does not — a statement other than `run`, an annotated or patterned `run` binder, a recursive definition, an explicit parameter block, a parameter named as a type variable, an annotation, a string interpolation, a grade, a type abstraction, a typed lambda parameter, a number with a fraction or an exponent, and every kind outside the dispatch table. `WrongSort`: the form produces another sort than its position demands. `Arity`: a lambda with other than one parameter, a block with no last computation.

`Unadmitted` and `Arity` exist because the grammar is the whole surface and the fragment is a small part of it; without them every form the surface has and the core lacks would be misreported as a sort error.

## Literals mean their decoded value

A number whose text is decimal digits lowers to its canonical non-negative magnitude, so `007` and `7` are one literal. A string lowers to the text between its quotes with its escapes decoded: `\n`, `\t`, `\r`, `\0`, `\\`, `\"` and `\'` to the character each names, a backslash before a line break elided together with the break, any other escaped character to itself, and a trailing lone backslash dropped. A literal whose text is not its form's lexeme is `MalformedLiteral`, which only a hand-built tree carries.

The alternative was to lower a string to its bytes verbatim. It was dropped because the core literal is the string the source means: two spellings of one string must lower to one core value, so that content identity in the core follows meaning. Reversal: a consumer that needs the written spelling reads it through the literal's origin span.

## One refusal per declaration

Every refusal found inside a declaration is offered to the declaration that owns the refusing node, and the declaration keeps the refusal at the lowest arena position, so the reported refusal does not depend on the order the passes visit nodes in. The declaration form's own faults sit at the declaration node itself and therefore outrank anything in its operands, and an attribute's tiles precede the declaration's operands, so an attribute's refusal outranks a refusal in its signature or body. A refused declaration lowers nothing but its attribute payloads, and every other declaration lowers regardless. Engine faults — an exhausted allowance, a tree of another grammar, a mold outside the grammar's table — abort the whole run instead, because no declaration's verdict can be trusted past one.

The alternative was to collect every refusal of a declaration. It was declined because later refusals under a refused form are frequently consequences of the first. Reversal: when a consumer reports all independent faults at once, a slot keeps a list ordered by position.

## The failure classifier

`LoweringRefusal::classify` is a `const`, wildcard-free match: adding a refusal variant fails to compile until its class is chosen. `MalformedSource` is the author's mistake; `Unrepresentable` is `OutOfFragment` alone; `EngineFault` is the budget, the grammar mismatch and the unknown mold. `UserAbsence` — what the author has not yet supplied, the only class that may become an obligation — has no refusal in it: obligations come from declaration shape, an uncompleted signature, and never from a classified failure.

## Attributes: a closed registry and a side table

The registry is closed: `checks` takes no payload, `owes` an integer, `refuses` a text. Five diagnostics cover what an attribute can get wrong, checked in this order: an unknown name, with the registered name within edit distance two when one exists; the same attribute written twice for one declared name, naming the first; a payload that is not a value at all, decided before the schema is consulted because being no value is a different fact from being the wrong one; a missing payload; and a payload of a form the schema does not admit, a payload on a marker included. A payload is read as a value under no binder, and the schema types it at the literal: an integer or a text.

An admitted attribute is filed under the content identity of the declaration form it decorates. The molded tree folds an attribute block into the declaration it decorates, so that identity covers the attributes themselves.

The alternative was a key independent of the attributes: a digest over the declaration with its attribute tiles excluded. It was declined because the syntax tree's digest is the one identity it carries, and a second digest would be a second hash of every declaration. Reversal: when a consumer must find a declaration's entries across an edit to its attributes alone, the key moves to a digest that excludes them.

An attribute is filed whatever its declaration's outcome: a refused declaration still has its tree and its digest, and an expectation about a refusal — `refuses` — can only be read off the declaration that refused. Its payload is minted for the same reason, the one part of a refused declaration that lowers. A declaration form whose own tiles fault records no half, and its attributes are not filed.

The alternative was to file attributes for unrefused declarations only. It was declined because it leaves every lowering refusal unexpectable: a fixture stating the refusal it expects would be read as stating nothing. Reversal: none while an attribute can state an expectation about its declaration's refusal.

## Origins for terms and types

Every minted core node records the syntax node that produced it — its arena position, its content identity and its span — for values, computations, value types and computation types alike, so a later note about a type has a carrier already, and whether the author wrote it or the lowering inserted it. A grouping mints nothing and its content keeps its own origin. A declaration's origin travels as an opaque `OriginToken` that a checker echoes back, which keeps spans and names out of the core.

## Two sweeps, no recursion, one allowance

The tree is laid out in level order, so ascending position order visits every parent before its children and descending order every child before its parent. The ascending sweep classifies and plans; the descending sweep mints, and can fail at nothing but the allowance, because every decision was made on the way down. Each is a plain loop: no descent, no frame stack, no depth a module can overflow. Every node visit, every binder frame walked, every module child and every attribute spends one step of the `LoweringBudget`; without it the binder walk would make lowering quadratic in a nesting depth nothing else bounds, and running out is an engine fault rather than a wrong answer.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
