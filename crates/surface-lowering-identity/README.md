# gandr-surface-lowering-identity

The identity family of gandr's lowering. It lowers path, bridge and flow types, the identity operations that a call's head spells, transports along a motive or a telescope, and the derived operations with the types they synthesise. The family compiles over `gandr-surface-lowering-base`, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's identity family. It classifies path, bridge and flow types and the relations that a type's head names. It reads the identity operation that a call's head spells, and it lowers reflexivity, extensionality, univalence, transports, composites, fills and the session and flow statements. It plans each derived operation, `back`, `then` and `cong`, and it synthesises the path type of one that states none.

**Why.** The lowering is the longest crate in the build of the driver. In a crate of its own, the family type-checks once. An edit of another family then does not type-check it again.

**How.** The family reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into another family. `gandr-surface-lowering` is the host, and a call from it into this family builds `Identities::new(self)`. Each call is static. A reading of the lowering, such as the minting of a transport, builds `IdentitiesRef::new(self)`, which borrows the host and never writes it. The family's tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Identities`: the family over its host, and each of its entries that the lowering calls ([`lower::identity`](src/lower/identity.rs)).
- `IdentitiesRef`: the family's reads over its host, each minting of a transport, a relation or a derived operation among them ([`lower::identity`](src/lower/identity.rs)).
- `spelled`: the reason that a call's head names no identity operation ([`lower::identity`](src/lower/identity.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the other families.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Identity types, identity operations, transports and derived operations | [`lower::identity`](src/lower/identity.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The family reads the lowering only through `Families`, a trait of the base, so the family compiles over the base alone.
- `vault:01a1b48c-2d17-7fc1-80ce-cb35e5cffd0e` — background: Ljungström and Mörtberg, LICS 2023, `arXiv:2302.00151` — § 2.2's action of a map out of a sphere on its cell.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
