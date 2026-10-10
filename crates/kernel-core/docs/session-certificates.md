# Session certificates and recorded flows

[Session-code formation and design choices](../README.md#session-code-identities) define the code vocabulary these certificates relate.

## Identity

`Value::SessionPath` introduces native `Path_U` by local bisimulation replay over supplied observable pairs, including extras. The kernel requires the root and continuation pairs, matching action directions, equal labels, and structurally equal payload codes or checked native payload paths. It never performs coinductive search; `core-session` supplies candidate relations. Admission keys commit all evidence even though conversion erases derivation pairs.

## Directed flows

`Flow::Session` checks Gay–Hole subtyping: source selections are a subset of target selections; target offers are a subset of source offers. Each consumer rechecks formation, simulation and payload proofs. This is forward-only evidence with no inverse or Path coercion. CBPV lowering refuses it as `RecordedRunRequired`; the [recorded-run consumer](../../core-session/README.md#certified-protocol-identities) supplies finite skeleton transport. Relation replay terminates over finite supplied data, not an observation budget that could declare an unfinished relation valid.

## Mutation scope

Session formation, relation replay, native traversal/content keys and recorded transport: omitted roots or continuations, wrong directions and label inclusions, escaped binders, unchecked payload paths, evidence-key collisions, dropped moves and changed digests. The six [memo binding conditions](../README.md#memo-binding-conditions) remain unchanged.
