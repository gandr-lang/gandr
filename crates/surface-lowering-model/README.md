# gandr-surface-lowering-model

The model and arity family of gandr's lowering. It lowers type families and the model signatures that they derive, packs a module as a model, plans the flattened model implicits, and mints reducts, forgettings and signature matches. It also lowers the arity of the type forms: telescopes, records, sums, observations, copatterns, selections and the groups of outputs. The family compiles over `gandr-surface-lowering-base`, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's model and arity family. It expands a type family where the source applies it, and it mints the type of each value component that a model signature derives. It packs a module as the record of a model, and it plans the model that answers each flattened model implicit. It reads the entries of each type form and mints the telescopes, records, sums, observations, copatterns and selections over them.

**Why.** The lowering is the longest crate in the build of the driver. In a crate of its own, the family type-checks once. An edit of another family then does not type-check it again.

**How.** The family reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into another family. `gandr-surface-lowering` is the host, and a call from it into this family builds `Models::new(self)`. Each call is static. A reading of the lowering, such as the minting of a projection, builds `ModelsRef::new(self)`, which borrows the host and never writes it. The family's tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Models`: the family over its host, and each of its entries that the lowering calls ([`lower::model`](src/lower/model.rs)).
- `ModelsRef`: the family's reads over its host, each minting of a projection, a record or a model type among them ([`lower::model`](src/lower/model.rs)).
- The arity of the type forms, on the same two types ([`lower::arity`](src/lower/arity.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the other families.
- **`hotpath`.** Off by default. It times a model slot's candidates and a reduct's maps for the benchmark report.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Type families, derived model signatures, packing, model implicits, reducts, forgettings and signature matches | [`lower::model`](src/lower/model.rs) |
| Telescopes, records, sums, observations, copatterns, selections and groups of outputs | [`lower::arity`](src/lower/arity.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The family reads the lowering only through `Families`, a trait of the base, so the family compiles over the base alone.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design, its declaration of a carrier as a member family of computation type, which `lower::model` lowers.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — background: the model-side row of a theory's generators, which `lower::model::derived` reads to leave out each filler that the theory derives.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
