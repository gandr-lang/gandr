# gandr-core-term

The core language and its one unified context: call-by-push-value syntax in a flat arena, the two-zone typing context every rule reads, the per-scope definitional environment, and the arena-free definition chain a normalizer lowers.

It holds **syntax and contexts only** — no elaborator, no value domain, no evaluation, no conversion. It is `no_std` over `core` and `alloc` and depends on `gandr-kernel-strata` and `gandr-kernel-term` for leaf vocabularies alone.

## Plan-milestone mapping

This crate answers the **value-domain milestone** of the ratified normalizer-and-elaborator plan where that milestone says `core-term` with the one unified context. The milestone's five context changes map onto the modules one to one:

| plan clause | where it lives |
| ----------- | -------------- |
| one representation: flat, de Bruijn, id-addressed, name-free | `src/context.rs` |
| the two-zone `Γ; Σ` shape kept and flattened | `src/context.rs`, with the zone on the occurrence |
| the definition chain drops the pointer and keeps its property | `src/definition.rs`, carrying subterm-table entry indices |
| the definitional environment is per-scope from the start | `src/definition.rs` |
| the error-path context contract becomes single-valued | `src/context.rs`, asserted rather than described |

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

The syntax and the arena the context is written against are `src/syntax.rs` and `src/arena.rs`.

## What it provides

- **The core call-by-push-value vocabulary** — values and computations on the term side, value types and computation types on the type side — in this crate's own node enums, so an elaboration-only former (a mark, a typed hole, a pattern hole) enters here rather than widening the vocabulary the kernel is obliged to represent.
- **A flat arena in four typed id families**, with constructor-only minting so a child id is always strictly less than its parent's, and wholesale truncation to a watermark so a pass's intermediates are dropped in one step. Teardown is a flat per-family vector drop, total on any term depth.
- **The one unified context**: two flat zones with separate de Bruijn index spaces. `Γ` admits contraction — an occurrence spends nothing — and `Σ` does not: an occurrence consumes its slot, a second occurrence is refused, and closing a linear scope with the slot unspent is refused. The two refusals are the two halves of the linear discipline, and they are unit-tested rather than left vacuous until the deferred former that introduces `Σ` binders lands.
- **The definition chain**, carrying each definition's body as a canonical subterm-table entry index and its height computed in admission order. Both order conditions are enforced rather than assumed: an entry out of admission order is refused, and a body mentioning a position at or above its own is refused, which is what makes the height one forward pass rather than a fixed point.
- **The per-scope definitional environment**: a flat, id-addressed forest of scopes whose parent link always points at a strictly earlier scope, with an iterative outward walk taking the innermost override. A scope that states nothing answers with the declaration's own stance, so the empty environment degenerates to the flat one.

## Two decisions that shape the crate

**The alphabet is the kernel's; the grammar is this crate's.** Levels, base types, literals, sum sides, de Bruijn indices, admission positions and canonical subterm-table entry indices are re-used from the trusted base rather than restated. Sharing the alphabet keeps the erasure that carries a core term down to a kernel term an id remapping rather than a payload translation, and stops the two languages disagreeing about what a literal or a level _is_. Owning the grammar keeps the kernel's closed vocabulary closed.

**A variable names its zone.** The two zones have separate index spaces, so an occurrence that did not say which zone it counted in would be ambiguous. Nothing at today's vocabulary binds into the linear zone — the formers that do are the reified first-class stacks, which are deferred features — so carrying the zone now is what keeps the retrofit from reaching every occurrence site later.

## The contract attributes

The `# Specification` prose stays the statement of record. A combined `#[spec(...)]` attribute mirrors expressible requirements and postconditions; each predicate appears verbatim in its own prose clause. Thirteen of the crate's fifteen specification blocks carry one.

The attributes check both arena widenings, the wholesale truncation's four family lengths, the shared index arithmetic, the binder-closing depth and the type it returns, both non-consuming context lookups, the definition chain's lookup and its one-pass height computation, the scope narrowing, a fresh scope's id and empty override list, a stated stance, and the outward transparency walk. Four state their postcondition by an independent reading — a linear scan against the chain's binary search, an inward count against the shared offset arithmetic, a sum that recovers the depth against the body's subtraction chain, and an iterator walk against the body's bounded loop — rather than the body's own expression read back. No capture allocates, and nothing the attributes add runs in the ordinary lane.

`Context::open` and `Context::occurrence` stay prose-only and name their boundary in `provides`: `open`'s postcondition relates every previously bound index to where the same binder now sits, and `occurrence`'s no-other-slot-touched half quantifies over every slot of both zones, each observable only against an allocating entry snapshot. The requirements that stay prose are of the same kind — a family length's provenance, a watermark's arena identity, and which admission positions a subterm-table index names are not observations those calls can make. The context's failing operations state their post-failure state in prose and assert it in tests, because that property is "the context is unchanged by the failure", which a postcondition on a failing path does not observe.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Not provided

No evaluation, no readback, no conversion and no glued value domain. Those live in `gandr-core-nbe`, which consumes this vocabulary.

No traversal over the arena's edge relation. The walks that need one are the value domain's, and each decides the shape it wants rather than taking one guessed at here.

No effect rows and no grades. The plan's crate decomposition names them for this crate and the crate does not carry them, which is a statement about what is here rather than a claim that they are unnecessary.

No erasure down to the kernel vocabulary. The bridge that erases marks and refuses holes belongs to the elaborator, and it has nothing to erase while the elaboration-only formers are absent.

## Using it

`cargo test -p gandr-core-term --all-targets` runs the suite.

```rust
use gandr_core_term::Context;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

fn example() {
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let mut context = Context::new();

    // Go under a lambda's binder, type its bound occurrence twice, and close.
    context.open(Zone::Intuitionistic, unit);
    let first = context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let again = context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    assert_eq!(first, again);
    assert_eq!(Ok(unit), context.close(Zone::Intuitionistic));
}
```

## Theoretical ideas relied on

Call-by-push-value as the polarity discipline that makes "value" and "computation" two vocabularies rather than one with a purity annotation; de Bruijn representation as the form in which α-equivalence is syntactic identity, so no freshness invariant has to be maintained; the two-zone sequent shape, in which the linear zone is the type-level statement that a control capture cannot be naively duplicated; and hash-consing under structural equality as a canonical form, which is what makes a subterm-table entry index an arena-independent name for content.

## Primary references

- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Semantics Structures in Computation 2, Springer, 2003. `isbn:978-1-4020-1730-8` — the polarity split this vocabulary is organized around. Locator unverified: the ISBN identifies a printing and has not been checked against a title page.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4's hash-consed subterm DAG is the object a content id names, which is why the definition chain can carry a table entry index across arenas.

## License

Apache-2.0 WITH LLVM-exception.
