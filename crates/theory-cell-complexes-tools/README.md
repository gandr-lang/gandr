# gandr-theory-cell-complexes-tools

The test-facing second inhabitant of the cell-alphabet trait — a first-order toy alphabet whose terms nest commands — and the adversary frame whose alphabets each break one law.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Toy alphabet](#toy-alphabet)
- [Adversary frame](#adversary-frame)
- [Test-only by construction](#test-only-by-construction)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `ToyAlphabet` implements `CellAlphabet` over a single-sorted term language of `Zero`, `Succ`, `Add` and metavariables, with every subterm a command position. `Lying<L>` is that alphabet in every answer but the ones an `AlphabetLie` overrides; `IncomparablePositions` calls every position pair disjoint, `NonLocalSplice` disturbs the sibling of the position it splices, `WithheldConvexity` withholds the convexity warrant, and `CollidingAddresses` hashes every orientation tag to nothing. The crate's own suite asserts the three inhabitant laws over the sequent alphabet and the toy, the copy search over the toy, and each adversary's one lie.

**Why.** The workspace ships one production alphabet, whose only command position is the root. An engine generic over `CellAlphabet` measured over that alphabet alone measures that alphabet, and never meets two applications inside one term. A second inhabitant with nested commands gives every engine suite a term language where positions below the root, overlaps between them and splices into them exist; an adversary gives the defensive checks of an engine an input that reaches them, which no honest inhabitant does.

**How.** A toy term is one flat table in prefix order, so every walk over it is a loop. Matching, unification, anti-unification, reading and splicing run over index ranges into that table; anti-unification walks the members' tables in lockstep and emits the generalization in prefix order. `Lying<L>` reuses the toy's associated types, its orientation tag wrapped in `LyingOrient<L>`, and forwards every method to `ToyAlphabet` except `position_order`, `splice_cmd_at` and `convexity_discharge`, which it forwards to `L`, as `LyingOrient<L>` forwards its hash; `AlphabetLie` gives each the honest answer by default, so an adversary overrides exactly the method it lies about.

## References

- Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge University Press, 1998. `doi:10.1017/CBO9781139172752` — first-order terms, positions and their prefix order, matching and syntactic unification with the occurs check, and the critical-pair lemma, whose case of rewrites at disjoint positions is what `IncomparablePositions` and `NonLocalSplice` each falsify from a different side.

## Provided features

- `ToyAlphabet`, `Toy`, `ToyVar`, `ToyPos`, `ToySubst`, `ToyOrient`, `ToyProv`, `ToyMeta`, `toy_cell`: the toy inhabitant, its terms and tags, and a rule-cell constructor. Witnesses: `tests::inhabitant::matching_then_substituting_returns_the_matched_term`, `tests::inhabitant::a_successful_match_binds_every_metavariable_the_pattern_names`, `tests::inhabitant::splicing_at_a_position_agrees_with_reading_it`, `tests::inhabitant::the_copy_search_is_alphabet_neutral`, `tests::inhabitant::each_member_is_its_generalization_under_its_arms`, `tests::inhabitant::a_repeated_disagreement_stands_one_point`, `tests::inhabitant::a_point_takes_a_name_no_member_wears`, `tests::inhabitant::a_family_without_a_generalization_is_refused_by_name`.
- `Lying`, `AlphabetLie`, `LyingOrient`, `IncomparablePositions`, `NonLocalSplice`, `WithheldConvexity`, `CollidingAddresses`, `lying_cell`, `reoriented_lying_cell`: the adversary frame and its four lies. Witnesses: `tests::adversary::the_incomparable_wrapper_breaks_the_position_order_and_keeps_the_match`, `tests::adversary::the_non_local_splice_wrapper_breaks_the_splice_and_keeps_the_read`, `tests::adversary::the_withheld_convexity_wrapper_withholds_the_warrant_and_keeps_the_match`, `tests::adversary::the_colliding_addresses_wrapper_hides_the_orientation_and_keeps_the_cell`.
- No production edge: the resolved workspace reaches this crate through no normal or build dependency. Witness: `tests::workspace::no_production_crate_links_the_tools_crate`.

## Expected features

- **A dev-dependency edge.** A consumer names this crate under `[dev-dependencies]` only; a normal or build edge fails the workspace witness.
- **Cargo and a resolved lockfile at test time.** The workspace witness runs `cargo tree --offline --locked` through the `CARGO` the test harness provides, so the test run needs the committed lockfile and the dependency sources already fetched, as any locked build does.

## Examples

Match a toy pattern below which a command nests, and reproduce the target.

```rust
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToySubst;

fn example() {
    // Add(Zero, x) against Add(Zero, Succ(Zero))
    let pattern = Toy::add(Toy::zero(), Toy::var("x"));
    let target = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let mut subst = ToySubst::default();
    assert!(bool::from(ToyAlphabet::match_cmd(&pattern, &target, &mut subst)));
    assert_eq!(target, ToyAlphabet::apply_subst(&subst, &pattern));
}
```

Ask the same position question of the honest alphabet and of the adversary that lies about it.

```rust
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::ToyAlphabet;

fn example() {
    let root = ToyAlphabet::root_position();
    let child = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
    assert_eq!(PositionOrder::Encloses, ToyAlphabet::position_order(&root, &child));
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&root, &child),
    );
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-cell-complexes-tools
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-cell-complexes-tools
```

Nontrivial operations carry executable `#[spec]` predicates and crate-local `# Adequacy` witnesses. They cover prefix-table bounds, transactional refusals, substitution chains, fresh names, empty and singleton generalization families, and the root-versus-child boundaries of each adversary. Predicates on an adversarial override state its intended lie rather than the alphabet law it breaks.

The const count operation and opaque variable iterator state their instrumentation limits. The alphabet marker, orientation wrapper, opaque hash-write protocols and unrestricted strategy delegation state the observations their interfaces cannot expose to an independent predicate. Their adequacy witnesses observe reconstructed terms, exact byte streams, distinct store identities and typed refusals.

## Toy alphabet

Every subterm of a toy term is a command, so `command_positions` lists every node breadth first, the root first. That is the property the crate exists for: the sequent alphabet's only command position is the root, so the splice law below the root, two applications in one term, and an overlap strictly inside a left-hand side are unreachable over it.

A term is one `Vec` of nodes in prefix order rather than a tree of boxes, matching the substrate's own pattern representation: no walk recurses, and a term of any depth is matched, read, spliced and dropped in a loop. A node's children are found by skipping subterm ends, which is linear in the term; the terms an engine suite builds are a few nodes, so no child index is kept.

The reduction order is size guarded by hole domination: the larger side wins when it carries every metavariable of the smaller at least as often, and every other pair, a tie included, is an obstruction. The order is well-founded and stable under substitution, which is all the trait asks; it has no tie-break, because the suites need an orientable rule and an obstruction, not a total order. Every cell may fire anywhere; the firing discipline is the sequent alphabet's to exercise. Renaming apart primes a name until it is fresh against the anchor and the other fresh names, so a cell already apart comes back unchanged.

## Adversary frame

An engine generic over `CellAlphabet` spends clauses of the trait it cannot check, and some of its checks exist only to catch an inhabitant that breaks one. Such a check is dead code over every honest inhabitant. `Lying<L>` makes it live: it is the toy alphabet with exactly one answer replaced, so a behaviour seen over `Lying<L>` and not over `ToyAlphabet` is attributable to `L`'s lie alone. Each adversary has a fixture witness here, asserting that its lie happens and that a neighbouring answer stays honest, so an adversary that drifted into a second lie fails in this crate rather than silently changing what every suite over it measures.

The frame carries four lies. The first two break a clause `CellAlphabet` states, the two an engine's commutation check defends against; the last two give an answer the trait permits and no honest inhabitant gives, so the refusal that answer triggers has no other input:

| Adversary | What it does | What an engine sees |
| --------- | ------------ | ------------------- |
| `IncomparablePositions` | breaks `position_order`'s clauses that a position is `Same` as itself and `Incomparable` only to a disjoint one | an application enclosing another licensed to commute with it |
| `NonLocalSplice` | breaks `splice_cmd_at`'s clause that a splice changes the term only at its position | two applications at disjoint positions that do not commute, though nothing an engine reads predicts it |
| `WithheldConvexity` | answers `convexity_discharge` with `ReCheckRequired` for every store, which an alphabet whose left-hand sides could match non-convexly owes | a commutation check's convexity conjunct refusing every pair |
| `CollidingAddresses` | hashes the orientation tag to nothing, which the `Hash` law permits for unequal values | two cells the store keeps apart, differing only in orientation, whose hashes collide, so a content address digested over them collides too |

A lie is added together with the engine check it exercises, never ahead of one: an adversary with no suite instantiating it measures nothing. Orientation is the narrowest place for a hash lie, because it enters a cell's derived hash and nothing else an engine reads to address the cell; `LyingOrient<L>` keeps the toy tag's equality and asks `L` only how it hashes, so every adversary but `CollidingAddresses` hashes a cell exactly as the toy cell with the same fields. The convexity warrant is restated rather than asked of the toy, because the trait reads it from a store of the alphabet's own cells.

`AlphabetLie` is a trait of static methods with honest defaults rather than a set of wrapper types, one per lie: one forwarding implementation of the 21-method trait serves every adversary, and an adversary is a unit struct overriding one method.

## Test-only by construction

This crate is reached through `[dev-dependencies]` only. Cargo cannot say so — the crate depends on the substrate alone, so a production crate depending on it closes no cycle — so `tests::workspace::no_production_crate_links_the_tools_crate` asks the resolver: `cargo tree --invert` over normal and build edges, from this crate, lists no other package. The alternative, a `test-support` feature on the substrate carrying the toy, loses: it puts the toy in the substrate's published surface, and feature unification lets any production build that enables it link the adversaries. The decision reverses if a second alphabet outside the tests needs the toy's term language as a real one; that alphabet is then a crate of its own, not a feature.

The crate is `no_std` and depends on `alloc`, the substrate and `quenchant-shape`; the workspace witness alone uses `std`, to run `cargo`.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
