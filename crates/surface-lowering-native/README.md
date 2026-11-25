# gandr-surface-lowering-native

The native family of gandr's lowering. It reads a data family where a type stands and applies a constructor to its fields. It seeds a data declaration's signature and compiles a match to native eliminations. The family compiles over `gandr-surface-lowering-base`, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's native family. It reads a data family where a type stands and applies a constructor to its fields. It seeds a data declaration's signature and compiles a match to native eliminations. It also reads a recursive call's descent and mints a theory's terms as a derived data declaration.

**Why.** The lowering is the longest crate in the build of the driver, and the native family is its largest part. In a crate of its own, the family type-checks once. An edit of another family then does not type-check it again.

**How.** The family reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into another family. `gandr-surface-lowering` is the host, and a call from it into this family builds `Native::new(self)`. Each call is static. The family's reads of the context alone stand on `NativeRef`, which borrows the context and never the lowering. The family's tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Native`: the family over its host, and each of its entries that the lowering calls ([`lower::native`](src/lower/native.rs)).
- `NativeRef`: the family's reads of the context alone ([`lower::native`](src/lower/native.rs)).
- `Joint`, `Staging`, `Decoded`, `Alone`, `Holds` and `Unwrapped`: the records the lowering reads of the family's answers ([`lower::native`](src/lower/native.rs)).
- `Columns`: a lambda's clauses, one column for each arrow of its stated type ([`lower::native::clauses`](src/lower/native/clauses.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the other families.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Data families, constructors, signatures and match compilation | [`lower::native`](src/lower/native.rs) |
| A lambda's clauses as columns | [`lower::native::clauses`](src/lower/native/clauses.rs) |

## References

- `vault:01a15620-7fbe-7030-a3af-07ffa620eed2` — anchor: the syntax bikeshed (§ Constructor names) — a bare constructor name that more than one family declares is refused, naming each family.
- `vault:01a156e3-93c7-7e62-9a50-b38b2da60284` — lineage: the loops and termination design (§ the decoder) — the fixpoint stages the code, and a decode carries no stage.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — lineage: the univalence design (§ The formers, and where each stands) — `Terms(S, Γ ⊢ s)` is a theory's initial model.
- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The family reads the lowering only through `Families`, a trait of the base, so the family compiles over the base alone.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
