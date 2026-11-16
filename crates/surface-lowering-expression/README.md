# gandr-surface-lowering-expression

The expression part of gandr's lowering. It plans and mints each expression and type form of a source. Its forms include sorts, function tails, blocks, insertions, universes, type operators, products, literals, paths, implicits, staged types, worlds and abstract components. It compiles over `gandr-surface-lowering-base` and the family crates, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's expression part. The first sweep plans each node of a source, and the second sweep mints its core node. The part reads data, models, capabilities, exits and identities through the families, and it assembles each lowered module's declarations, structures and scope.

**Why.** The expression part is the longest part of the lowering. In a crate of its own, it type-checks apart from the top, which holds the closure, the dispatch of the families and the entry points. An edit of the top then does not type-check it again.

**How.** The part reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into a family. `gandr-surface-lowering` is the host, and a call from it into this crate builds `Expressions::new(self)`. Each call is static. A reading of the lowering builds `ExpressionsRef::new(self)`, which borrows the host and never writes it. The tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Expressions`: the expression lowering over its host, and each of its entries that the top calls ([`lower`](src/lower.rs)).
- `ExpressionsRef`: the expression lowering's reads over its host ([`lower`](src/lower.rs)).
- `Finished` and `Resumed`: the tables that a module finishes with, and the tables that a module resumed after a closure leads with ([`lower`](src/lower.rs)).
- `Arguments`, `ENTRY` and `entry_shape`: the shapes of a program's entry ([`lower::entry`](src/lower/entry.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the families.
- **`hotpath`.** Off by default. It times a rule block's decision for the benchmark report.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Sorts, function tails, blocks, insertions, universes, type operators, products, literals, the two sweeps | [`lower`](src/lower.rs) |
| The cut of an early exit, inferred exits and nested computations | [`lower`](src/lower.rs) |
| Type members, abstract components and opaque ascription | [`lower::sealing`](src/lower/sealing.rs) |
| Paths, their functions and round trips | [`lower::path`](src/lower/path.rs) |
| Implicit parameters and their supplies | [`lower::implicit`](src/lower/implicit.rs) |
| Stages, regions and staged types | [`lower::staged`](src/lower/staged.rs), [`lower::patched`](src/lower/patched.rs) |
| Functor applications | [`lower::functor`](src/lower/functor.rs) |
| Worlds | [`lower::world`](src/lower/world.rs) |
| Boundary checks of a layout | [`lower::boundary`](src/lower/boundary.rs) |
| Univalence and strata | [`lower::ua`](src/lower/ua.rs) |
| A program's entry | [`lower::entry`](src/lower/entry.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The part reads the lowering only through `Families`, a trait of the base, so it compiles over the base and the family crates alone.
- `vault:01a178aa-6cd7-7ac2-a049-ee4124ad5576` — background: the layouts design — a boundary check is the layout program's verdict.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: `compose[n, k]` reads its stratum as `ua[n, k]` does.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
