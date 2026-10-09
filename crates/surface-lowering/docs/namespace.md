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

## An arena trie and no recursion

The trie is an arena: nodes in one vector, children sorted by segment, a freed node's slot reused, so detaching, grafting and merging a subtree cost its depth and size where a flat map keyed by whole paths scans every binding. A modifier is built only by its builders, into one post-order vector of constructors, so equality is structural and nothing is boxed. No walk recurses: insertion, lookup, iteration, equality, merging, detachment, scopes and sections, the interpreter and teardown run on heap worklists, and a chain one hundred thousand segments deep passes each inside a 64 KiB stack.

## The outermost scope

`Recognition` is the outermost scope. Ordered `SeedTable`s seed it, a later entry winning. `lower_module` declares every declared name over it in admission order, displacing the whole builtin subtree under the name, and reports every lambda, parameter and `run` binder against it without rebinding. Under `ShadowPolicy::WarnAndAllow` a source name over a builtin is recorded in `shadowed`; under `Reject` its declaration is refused as `ShadowedBuiltin`. `resolve_path` reports a path complete, an unknown member of the namespace governing its deepest resolved prefix, or ungoverned. The rows a prelude, a host and a session seed are held; callers pass `Recognition::default()`.

## Held tests

Tests whose readers do not exist yet are held, not written against stand-ins. Ten wait for the prelude and host tables: `the_outermost_scope_resolves_every_prelude_and_host_name`, `only_a_host_member_is_call_only`, `a_parameter_named_for_a_host_module_reports_and_still_resolves_to_the_host`, `every_prelude_selection_resolves_identically_through_the_scope`, `every_host_call_resolves_identically_through_the_scope`, `every_declined_selection_is_declined_identically`, `an_extern_declaration_shadows_a_host_module_and_reports_it`, `member_paths_agree_with_the_seeded_scope`, `host_module_members_resolve_in_their_sig` and `host_lookup_by_position_is_exact`. Three wait for a session that carries the scope from one submission to the next: `a_session_rejects_a_shadowed_builtin_under_policy`, `a_session_carries_a_shadowing_declaration_into_the_next_submission` and `import_namespace_carries_across_lines_and_resolves_source_declarations`.
