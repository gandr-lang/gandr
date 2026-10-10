# gandr-theory-virtual-doctrines

Virtual double categories, reflected judgments and directed laws over replayable rewriting evidence.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Reflection and replay](#reflection-and-replay)
- [Flat syntax and borrowed checking](#flat-syntax-and-borrowed-checking)
- [Directed and finite laws](#directed-and-finite-laws)
- [Law witnesses](#law-witnesses)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A split virtual-double-category interface over signatures, generator renamings, relations and derivations, with a reflected protype/proterm calculus. The concrete interpretation reads a cell store, compares transformations by replay and exposes the constructor menu as queries over rewriting evidence.

**Why.** Relations, their restrictions and their composites need an identity criterion stronger than matching syntax or matching endpoints. Reflected judgments also need to distinguish formation errors, checking-only forms and invalid certificates. Keeping those questions above the rewriting engine lets the reflection reuse the engine's actual matching, overlap and replay semantics.

**How.** Signatures, protypes, proterms and derivations use flat trees shared with the description tier. Formation and bidirectional checking walk borrowed nodes with explicit worklists. A description registry stores real `SignDesc<G>` values without interpreting the consumer's grade type. Grafts elaborate into sequential certificates; queries read overlap families and normalizing paths; directed cuts select the invertible or acyclicity-checked composition operation.

## References

- Hayato Nasu. _Logical Aspects of Virtual Double Categories_. Preprint, January 2025. `arXiv:2501.17869` — split cartesian fibrant virtual double categories, their internal language and protype isomorphisms.
- Nicolas Behr, Russ Harmer and Jean Krivine. “Concurrency Theorems for Non-linear Rewriting Theories.” _International Conference on Graph Transformation (ICGT 2021)_, 2021. `arXiv:2105.02842` — overlap-indexed composition and the distinction between a family of composites and a chosen composite.

## Provided features

- `Vdc`, `CellStoreVdc`, `SignatureRef`, `SigMorphism`, `RelationRef`, `Derivation` and `DescTable<G>`: the category interface, its cell-store interpretation and its description namespace.
- `WCartesianAction`: independently reported projection, diagonal and product-structure obligations, including malformed boundaries.
- `Protype`, `Proterm`, `Context` and `Checker`: formation, bidirectional checking, synthesis, scoped hypotheses and certificate replay. Errors retain their typed boundary evidence.
- `Query`: budgeted rewrite paths, path folds, overlap-indexed seam families, confluence candidates and relation tabulators.
- `IsoWitness` and `ProtypeIso`: paired certificate witnesses whose two round trips are checked by engine replay.
- Directed contexts, directed hom and restricted J, finite discrete ends and coends, Fubini, co-Yoneda and metadata-sensitive directed cut.

## Expected features

- **A cell store and derivation environment.** The consumer owns the engine cells and the indexed certificates that reflected syntax names.
- **Formed judgments.** Run `check_protype` on an expected protype before checking its inhabitants. `check` and `synth` are judgments over the supplied context and hypotheses; they do not repeat the entire formation pass.
- **Description grades.** `DescTable<G>` retains the real description's grade parameter. The reflection does not replace it with a core-specific grade or decode it into a second description type.
- **Explicit budgets.** Rewrite queries return their recorded prefix and distinguish exhaustion from reaching a normal form.

## Examples

Check a reflexive inhabitant through the public interface:

```rust
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_levitation::{FreeTerm, NominalId};
use gandr_theory_virtual_doctrines::{Checker, Context, Proterm, Protype, SignatureRef, TermRef};

let signature = SignatureRef::single(NominalId::new(0_u64.into(), "Ground"));
let point = TermRef::new(FreeTerm::ctor("A", []));
let expected = Protype::path(signature.clone(), point.clone(), point.clone());
let term = Proterm::refl(signature, point);
let cells = CellStore::new();
let checker = Checker::new(&[], &cells);
assert_eq!(checker.check_protype(&Context::new(), &expected), Ok(()));
assert_eq!(checker.check(&Context::new(), &[], &term, &expected), Ok(()));
```

Run the public-interface law suite in both configurations:

```sh
cargo nextest run -p gandr-theory-virtual-doctrines
RUSTFLAGS='--cfg anodized_panic' CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-theory-virtual-doctrines
```

## Reflection and replay

A relation names generating cells and remembers its two restriction frames. Tight composition is canonical renaming composition; restriction composes the frames in the split order. Cell equality compares the loose-arrow boundaries and then the engine transformations by replay, not by certificate allocation or syntax identity.

Elaboration admits identities, certificate leaves and sequential grafts with an agreeing seam. A graft with multiple nontrivial parallel inputs, or a broken sequential seam, yields `Elaborated::Stuck`. This is the supported interpretation of the derivation grammar, not an arbitrary choice of a parallel composite.

A certificate judgment requires a path or relation protype, a bound derivation and successful replay. It does not translate a reflected `TermRef` endpoint into a command pattern or claim that the recorded engine endpoints equal the reflected endpoints: those are distinct representations. Isomorphism validity separately checks both replaying round trips to identity.

- **Alternatives.** Structural equality of certificates confuses different replay-equivalent witnesses; endpoint equality alone admits fabricated paths. A second matcher in the reflection would duplicate the engine's semantics.
- **Reversal.** A shared, checked interpretation of reflected faces into engine commands can strengthen the certificate judgment with endpoint agreement. A different identity criterion requires corresponding replacement laws, rather than a silent change to replay equivalence.

## Flat syntax and borrowed checking

Every recursive syntax value is one flat tree, and every traversal uses an explicit worklist. Borrowed node views let checking compare protypes and signatures without cloning the successful judgment. Scope entries point to their parent binding, so an extension's local hypothesis neither leaks to a sibling nor destroys an outer binding when shadowed. Certificate leaves elaborate by borrowing their stored evidence; composition owns only the certificate it constructs.

- **Alternatives.** Recursively boxed syntax moves depth-sensitive work into traversal and destruction. Cloning the hypothesis environment at every lambda and cloning expected protypes at every child makes successful checking allocate in proportion to repeated subtree size.
- **Reversal.** A measured cost from concatenating flat tables during construction can justify a shared arena, provided structural equality, borrowed checking and bounded-stack destruction remain observable contracts.

## Directed and finite laws

An object variable has one directed variance. Engine producer and consumer metadata select the corresponding variance; a mixed hole cannot be assigned either one. Context lookup observes the innermost binding. Directed J accepts a covariant-target or constant motive and refuses the contravariant-source motive, including the proposed symmetry operation.

Ends and coends are products and coproducts over explicitly enumerated discrete carriers. Fubini swaps both carrier coordinates while preserving each payload. Co-Yoneda selects the first diagonal component and reports a named absence off the carrier. These operations do not assert naturality over non-discrete morphisms.

Directed cut reads every participating cell's current metadata. Entirely invertible evidence uses unconditional composition. Otherwise the decomposition-space engine decides the variable-flow obstruction. The law suite includes store-mediated reconvergence and a dropped seam hole: pairwise overlap data alone does not determine that verdict.

## Law witnesses

The integration target exercises the public surface rather than a second reflection implementation. Its named suites cover tight composition, split restriction, grafting, cartesian obligations, formation and judgment boundaries, query faces, isomorphism replay, directed laws and overlap-indexed composition and confluence factorization.

The floor retains 64 behavioral tests, including all 23 property tests. The accessor-only checks `pro_variable_name_round_trips` and `derivation_id_conversions_round_trip` are retired rather than promoted to behavioral witnesses; no behavioral floor row is deferred. Five additional witnesses cover judgment boundaries, replay-field corruption, deep syntax and generic description lookup.

The composition-family suite retains the explicit trivial-diagonal exception. Structural cell deduplication can leave a diagonal cospan with no proper overlap; the witness checks that classification rather than weakening a failed family assertion.

The constructor menu pairs every supported proterm form with an accepted judgment and its nearest invalid judgment. It also distinguishes both composition seam boundaries, undeclared object variables, unissued relation generators, checking-only forms, scoped hypotheses and corruption of real replay fields. A small-stack witness checks and drops a deeply nested syntax value. The generic registry witness distinguishes duplicate nominal identities and retains field grades without an upward dependency.

Executable predicates state their observed projection in each item's adequacy section. Generator membership alone is not family completeness; endpoint agreement alone is not replay; callback-driven induction is witnessed without re-invoking a potentially effectful callback in its predicate.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
