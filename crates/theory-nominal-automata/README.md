# gandr-theory-nominal-automata

Finite register presentations of nominal word and tree automata over caller-owned names.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Representation](#representation)
- [Model boundary](#model-boundary)
- [Behavioral floor](#behavioral-floor)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A symbolic automaton has finitely many controls, a register arity per control, and transitions that retain, allocate or erase names. Concrete configurations pair controls with partial injective stores.

**Why.** Resource-lifecycle traces need to distinguish a remembered name from a fresh allocation and to reject unmatched release or a live resource at an accepting boundary. Symbolic register rules express those conditions independently of any compiler name supply.

**How.** Constructors validate controls, arities, reads and injective transfers. Literal word membership follows a deduplicated frontier with iterative epsilon closure. Allocation-only word and tree handles share transfer validation; a flat term arena computes free names under lexical scope.

## References

- Lutz Schröder, Dexter Kozen, Stefan Milius and Thorsten Wißmann. _Nominal Automata with Name Binding_. Foundations of Software Science and Computation Structures, 2017. [arXiv:1603.01455](https://arxiv.org/abs/1603.01455) — allocation-only word automata.
- Simon Prucker and Lutz Schröder. _Nominal Tree Automata with Name Allocation_. International Conference on Concurrency Theory (CONCUR), 2024. [doi:10.4230/LIPIcs.CONCUR.2024.35](https://doi.org/10.4230/LIPIcs.CONCUR.2024.35) — tree rules, partial registers and name-bearing terms.
- Simon Prucker, Stefan Milius and Lutz Schröder. _Nominal Automata with Name Deallocation_. 2026. [arXiv:2603.24468](https://arxiv.org/abs/2603.24468) — lifecycle letters, name erasure and the session-monitor example.

## Provided features

| Surface | Behavior |
| ------- | -------- |
| `handle` | Nominal indices, typed structural errors, partial injective stores and register transfers. |
| `letter::Letter` | Free use, allocation, release and immediate release. |
| `nda::Nda` | Validated word automata and literal membership, including nondeterministic and epsilon transitions. |
| `nda::name_dropping` | One epsilon erasure per register; retained original transitions preserve the donor language. |
| `rnna::Rnna` | Validated allocation-only word handles. |
| `rnta::Rnta` | Validated allocation-only tree handles with ordered child transfers. |
| `rnta::Term` | Flat, acyclic term arena with lexical free-name computation. |

## Expected features

Names implement `Copy + Ord` with stable equality and ordering. Their identity belongs to the caller; the crate neither mints names nor assigns a unification role. Tree symbols are caller-owned values. The library is `no_std` and needs `alloc`. Optional executable specifications are selected graph-wide by `--cfg anodized_panic`.

## Examples

`cargo run -p gandr-theory-nominal-automata --example lifecycle` executes a two-control monitor and checks a drained trace, a leak and an unmatched release.

Run the public-API floor in both modes:

```sh
cargo test -p gandr-theory-nominal-automata --all-targets
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing \
  cargo test -p gandr-theory-nominal-automata --all-targets
```

## Representation

**Caller-owned names.** The automaton is generic over name identity rather than coupled to a fresh-name allocator. This keeps lifecycle reasoning independent of de Bruijn indices, admission positions and compiler allocation policy. Alternative: a crate-owned sort-tagged supply; it adds identity machinery the automaton never needs. Reversal: an automaton operation must generate globally fresh identities rather than check supplied names.

**Flat terms.** Child indices point to earlier arena entries. Traversal, cloning and destruction have no ownership recursion. Sharing denotes repeated occurrences, so a shared node can be free in one scope and bound in another. Alternative: recursively owned child terms; depth-dependent clone and drop would violate the arena's totality boundary. Reversal: a different flat storage representation demonstrably reduces cost while preserving lexical observations.

**Validated transfers.** Retained source registers must exist and occur at most once in each target transfer. Allocation appears at most once and only on allocating rules. Close and epsilon-drop rules cannot retain the erased register. Each tree child validates independently: separate child stores may each retain the allocated name. These checks make internal transfer application preserve partial injectivity. Alternative: validate every resulting store at runtime; that repeats structural work on every input letter. Reversal: an event-dependent transfer representation needs dynamic validation.

**Lossless indices.** Controls, registers, arities and degrees wrap `usize`; vector lengths never saturate into a narrower identity. Register lookup distinguishes an empty slot from an out-of-range register through `Maybe` and `RegisterAbsent`.

## Model boundary

The word runner decides literal membership for supplied traces. Name dropping adds epsilon erasures over partial stores; the directed remembered-name example witnesses its effect on an alpha variant. The finite suite does not establish a general nominal-language theorem.

Allocation-only word and tree surfaces validate symbolic handles. Tree rules carry their rank through their ordered child targets; symbols have no separately declared global rank table. Tree execution, bounded-alphabet reduction, emptiness, inclusion, equivalence, determinization and expression compilation belong to the classical back end. A static theorem catalogue is documentation, not an implemented procedure.

## Behavioral floor

The named floor contains **25 ported**, **5 deferred** and **5 retired** obligations. Ported rows retain their names and execute through the public API in one automatically discovered integration target. The bounded language-enlargement witness exhausts all 2,396,745 words of length at most seven over eight letters, retaining the full input-length bound. Three additional behavioral witnesses cover malformed transfers across all models, cyclic epsilon closure with nondeterministic branching, and 10,000-deep flat terms.

Retired rows are metadata or forwarding assertions excluded by the behavioral-testing rule; their associated semantic behavior is observed by lifecycle runs, store validation and lexical scope witnesses. Deferred rows await **the classical back end**, not a replacement placeholder.

| Obligation | Status | Evidence or reader |
| ---------- | ------ | ------------------ |
| `handle::duplicate_assignment_is_rejected` | Ported | `tests::handle::duplicate_assignment_is_rejected` |
| `handle::injective_partial_store_is_accepted` | Ported | `tests::handle::injective_partial_store_is_accepted` |
| `handle::empty_store_has_only_empty_registers` | Ported | `tests::handle::empty_store_has_only_empty_registers` |
| `nda::session_monitor_accepts_drained_log` | Ported | `tests::nda::session_monitor_accepts_drained_log` |
| `nda::session_monitor_rejects_leaked_login` | Ported | `tests::nda::session_monitor_rejects_leaked_login` |
| `nda::session_monitor_rejects_logout_without_login` | Ported | `tests::nda::session_monitor_rejects_logout_without_login` |
| `nda::session_monitor_rejects_unknown_actor` | Ported | `tests::nda::session_monitor_rejects_unknown_actor` |
| `nda::session_monitor_bounds_concurrent_logins` | Ported | `tests::nda::session_monitor_bounds_concurrent_logins` |
| `nda::session_monitor_degree_is_maximum_arity` | Ported | `tests::nda::session_monitor_degree_is_maximum_arity` |
| `nda::construction_rejects_invalid_control` | Ported | `tests::nda::construction_rejects_invalid_control` |
| `nda::construction_rejects_arity_mismatch` | Ported | `tests::nda::construction_rejects_arity_mismatch` |
| `nda::construction_rejects_unknown_register` | Ported | `tests::nda::construction_rejects_unknown_register` |
| `nda::construction_rejects_misplaced_allocated_name` | Ported | `tests::nda::construction_rejects_misplaced_allocated_name` |
| `nda::construction_rejects_kept_deallocated_name` | Ported | `tests::nda::construction_rejects_kept_deallocated_name` |
| `nda::open_close_allocates_and_immediately_forgets` | Ported | `tests::nda::open_close_allocates_and_immediately_forgets` |
| `rnna::construction_accepts_a_well_formed_rnna` | Ported | `tests::rnna::construction_accepts_a_well_formed_rnna` |
| `rnna::construction_rejects_misplaced_allocated_name` | Ported | `tests::rnna::construction_rejects_misplaced_allocated_name` |
| `rnta::free_names_respects_binder_shadowing` | Ported | `tests::rnta::free_names_respects_binder_shadowing` |
| `rnta::construction_accepts_a_well_formed_rnta` | Ported | `tests::rnta::construction_accepts_a_well_formed_rnta` |
| `rnta::construction_rejects_unknown_register` | Ported | `tests::rnta::construction_rejects_unknown_register` |
| `rnta::construction_rejects_misplaced_allocated_name` | Ported | `tests::rnta::construction_rejects_misplaced_allocated_name` |
| `dropping::literal_language_is_not_alpha_closed_before_dropping` | Ported | `tests::dropping::literal_language_is_not_alpha_closed_before_dropping` |
| `dropping::name_dropping_closes_language_under_alpha` | Ported | `tests::dropping::name_dropping_closes_language_under_alpha` |
| `dropping::name_dropping_adds_one_drop_rule_per_register` | Ported | `tests::dropping::name_dropping_adds_one_drop_rule_per_register` |
| `dropping::name_dropping_only_enlarges_the_language` | Ported | `tests::dropping::name_dropping_only_enlarges_the_language` |
| `classical::nfta_emptiness_returns_a_verifiable_bottom_up_witness` | Deferred | The classical back end. |
| `classical::nfta_emptiness_rejects_final_states_without_a_bottom_up_run` | Deferred | The classical back end. |
| `classical::s_restriction_orders_atoms_and_encodes_letters` | Deferred | The classical back end. |
| `classical::emptiness_returns_shortest_deterministic_witness` | Deferred | The classical back end. |
| `classical::inclusion_returns_deterministic_counterexample` | Deferred | The classical back end. |
| `catalogue::every_model_covers_the_four_core_problems` | Retired | Static catalogue coverage, not automaton behavior. |
| `catalogue::decidable_entries_name_construction_and_citation` | Retired | Citation-string presence, not automaton behavior. |
| `catalogue::headline_facts_are_registered` | Retired | Static catalogue entries, not executable decision procedures. |
| `handle::configuration_exposes_control_and_store` | Retired | Constructor/accessor forwarding without a semantic boundary. |
| `handle::atom_path_is_exercised` | Retired | Import-path and sort-accessor wiring. |

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
