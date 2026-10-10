# The namespace engine

The `namespace` module of `gandr-surface-lowering`: hierarchical names, the trie that holds them, the modifier language that rewrites one, the events a handler settles, scopes with their sections, and the outermost scope lowering declares names over. The crate's [README](../README.md) states the rest of the crate, why the engine sits in it, and lists every feature with its witnesses.

<!-- toc -->

- [Namespaces, modifiers and scopes](#namespaces-modifiers-and-scopes)
- [An arena trie and no recursion](#an-arena-trie-and-no-recursion)
- [The outermost scope](#the-outermost-scope)
- [Held tests](#held-tests)

<!-- tocstop -->

## Namespaces, modifiers and scopes

`namespace` follows yuujinchou (see the README's [references](../README.md#references)). A namespace is a finite trie from hierarchical names to bindings; a modifier — `all`, `id`, `none`, `only`, `except`, `renaming`, `in`, `seq`, `union`, `hook` — rewrites one through six core constructors and one interpreter; every not-found, shadow and hook event goes to a `NamespaceEventHandler` at the full path where it happened, so a policy is a handler, never an engine change. A `Scope` holds a visible and an export namespace and a stack of sections: an import reaches the visible namespace, an include both, and closing a section includes its export under a prefix once a modifier has chosen what passes.

`NamePath` compares and composes opaque segments, not their diagnostic rendering. The dotted boundary maps the empty string to the root and splits every nonempty string at each period, retaining empty and Unicode segments. A raw segment may itself contain a period; it stays one segment through composition and prefix removal. Display writes the root as `.` and is not an inverse of the dotted boundary. A formatter refusal stops rendering and is returned to the caller.

The permissive handler appends one record per callback in execution order. Clearing starts a fresh log without changing the policy: a later binding still wins a collision and a hook still returns its subject. Runtime predicates check event kind, full path, append count and retained binding count without adding equality bounds to generic labels or payloads; bounded interpreter witnesses check those values. Required callback contracts describe how the interpreter uses their outcomes, not properties a callback can establish about a future run.

Imports and modifiers commit their target namespace only on success. Includes merge visible before export and retain entries merged before a refusal. Closing a section consumes it before running the closing modifier: modifier refusal restores the parent unchanged, while merge refusal keeps the partial include in that parent. Neither failure reopens the section; a later close reports `NoOpenSection`. Scope predicates check namespace counts and section-stack transitions without requiring equality or cloning generic payloads; the witnesses check exact retained bindings.

## An arena trie and no recursion

The trie is an arena: nodes in one vector, children sorted by segment, a freed node's slot reused, so detaching, grafting and merging a subtree cost its depth and size where a flat map keyed by whole paths scans every binding. A modifier is built only by its builders, into one post-order vector of constructors, so equality is structural and nothing is boxed. No walk recurses: insertion, lookup, iteration, equality, merging, detachment, scopes and sections, the interpreter and teardown run on heap worklists, and a chain one hundred thousand segments deep passes each inside a 64 KiB stack.

Trie predicates check count conservation across moves, fresh versus repeated insertion, edge selection, vacant-slot transitions and yielded binding identity without cloning payloads. Exact-map witnesses cover reuse independently of arena layout and preserve non-unit tags through relocation and collision. Tags are opaque to binding operations but participate in equality and debugging. Governed lookup stops at the first unbound nonempty prefix: a binding at the root does not bridge a gap.

Modifier predicates check operand relocation, the checked selection and renaming expansions, and a nonempty post-order arena at interpreter entry. Each step checks its continuation and namespace-count transition. These checks do not replay handlers or clone their payloads: hooks may replace a namespace arbitrarily, while nested event paths and branch isolation are observed by the interpreter witnesses. The alias builder remains a direct checked-renaming adapter; its witnesses exercise qualification and refusal rather than pinning the forwarding call.

## The outermost scope

`Recognition` is the outermost scope. Ordered `SeedTable`s seed it, a later entry winning. `lower_module` declares every top-level declaration over it in admission order, then every top-level module as a namespace governing exactly the components it exports, each displacing the whole builtin subtree under its name, and reports every lambda, parameter and `run` binder against it without rebinding. Under `ShadowPolicy::WarnAndAllow` a source name over a builtin is recorded in `shadowed`; under `Reject` its declaration is refused as `ShadowedBuiltin`. `resolve_path` reports a path complete, an unknown member of the namespace governing its deepest resolved prefix, or ungoverned, and the lowering reads a module path through it. The rows a prelude, a host and a session seed are held; callers pass `Recognition::default()`.

Recognition predicates check last-wins seed coordinates, governed-prefix classification and shadow-log transitions without cloning the namespace. Shadow policy follows the binding's site tag, independently of its recognized kind: a builtin-tagged arrival has no source span to record, while a source-tagged arrival over a builtin records its exact span under warning policy. Seeded roots do not bridge unbound prefixes. Rejected declarations preserve visible names; binder checks never bind; resumption preserves names and starts a fresh log.

## Held tests

Tests whose readers do not exist yet are held, not written against stand-ins. Ten wait for the prelude and host tables: `the_outermost_scope_resolves_every_prelude_and_host_name`, `only_a_host_member_is_call_only`, `a_parameter_named_for_a_host_module_reports_and_still_resolves_to_the_host`, `every_prelude_selection_resolves_identically_through_the_scope`, `every_host_call_resolves_identically_through_the_scope`, `every_declined_selection_is_declined_identically`, `an_extern_declaration_shadows_a_host_module_and_reports_it`, `member_paths_agree_with_the_seeded_scope`, `host_module_members_resolve_in_their_sig` and `host_lookup_by_position_is_exact`. Two wait for a session that carries a shadow policy and a shadowing declaration from one submission to the next: `a_session_rejects_a_shadowed_builtin_under_policy` and `a_session_carries_a_shadowing_declaration_into_the_next_submission`.
