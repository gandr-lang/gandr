# gandr-theory-cell-complexes-tools

The test-facing second inhabitant of the cell-alphabet trait — a first-order toy alphabet whose terms nest commands — and the adversary frame whose alphabets each break one law.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `ToyAlphabet` implements `CellAlphabet` over a single-sorted term language of `Zero`, `Succ`, `Add` and metavariables, with every subterm a command position. `Lying<L>` is that alphabet in every answer but the ones an `AlphabetLie` overrides; `IncomparablePositions` calls every position pair disjoint, `NonLocalSplice` disturbs the sibling of the position it splices, `WithheldConvexity` withholds the convexity warrant, and `CollidingAddresses` hashes every orientation tag to nothing. The crate's own suite asserts the three inhabitant laws over the sequent alphabet and the toy, the copy search over the toy, and each adversary's one lie.

**Why.** The workspace ships one production alphabet, whose only command position is the root. An engine generic over `CellAlphabet` measured over that alphabet alone measures that alphabet, and never meets two applications inside one term. A second inhabitant with nested commands gives every engine suite a term language where positions below the root, overlaps between them and splices into them exist; an adversary gives the defensive checks of an engine an input that reaches them, which no honest inhabitant does.

**How.** A toy term is one flat table in prefix order, so every walk over it is a loop. Matching, unification, anti-unification, reading and splicing run over index ranges into that table; anti-unification walks the members' tables in lockstep and emits the generalization in prefix order. `Lying<L>` reuses the toy's associated types, its orientation tag wrapped in `LyingOrient<L>`, and forwards every method to `ToyAlphabet` except `position_order`, `splice_cmd_at` and `convexity_discharge`, which it forwards to `L`, as `LyingOrient<L>` forwards its hash; `AlphabetLie` gives each the honest answer by default, so an adversary overrides exactly the method it lies about.

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

Nontrivial operations carry executable `#[spec(...)]` predicates and crate-local `# Adequacy` witnesses. They cover prefix-table bounds, transactional refusals, substitution chains, fresh names, empty and singleton generalization families, and the root-versus-child boundaries of each adversary. Predicates on an adversarial override state its intended lie rather than the alphabet law it breaks.

The count successor retains its const interface; an inner-field predicate enforces the ordinary increment and the saturated boundary. The opaque variable iterator states its instrumentation limit. The alphabet marker, orientation wrapper, opaque hash-write protocols and unrestricted strategy delegation state the observations their interfaces cannot expose to an independent predicate. Their adequacy witnesses observe reconstructed terms, exact byte streams, distinct store identities and typed refusals.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The toy alphabet | [`toy`](src/toy.rs) |
| The adversary frame | [`adversarial`](src/adversarial.rs) |
| Test-only by construction, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
