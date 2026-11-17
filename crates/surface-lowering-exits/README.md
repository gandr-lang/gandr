# gandr-surface-lowering-exits

The exits family of gandr's lowering. It commutes an early exit to where its body ends. It lowers a loop's fixpoint, its `break`, its `continue` and its re-entry, and it reads the runs that a computation asks for. The family compiles over `gandr-surface-lowering-base`, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's exits family. It surveys what the paths of each node do with the body that the node stands in. It classifies each early exit and commutes it to where its body ends. It lowers each loop as a fixpoint, with its `break`, its `continue` and its re-entry. It also reads the runs that a computation asks for: inferred, linear and nested.

**Why.** The lowering is the longest crate in the build of the driver. In a crate of its own, the family type-checks once. An edit of another family then does not type-check it again.

**How.** The family reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into another family. `gandr-surface-lowering` is the host, and a call from it into this family builds `Exits::new(self)`. Each call is static. A reading of the lowering, such as the minting of a body, builds `ExitsRef::new(self)`, which borrows the host and never writes it. The family's tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Exits`: the family over its host, and each of its entries that the lowering calls ([`lower::exits`](src/lower/exits.rs)).
- `ExitsRef`: the family's reads over its host, each minting of a body or a loop among them ([`lower::exits`](src/lower/exits.rs)).
- `unwind`: a `return` in a handled subject, as the capture that leaves its body ([`lower::exits`](src/lower/exits.rs)).
- `again`: a loop's own name for its next iteration ([`lower::loops`](src/lower/loops.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the other families.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The survey, the classification and the commuting of early exits | [`lower::exits`](src/lower/exits.rs) |
| A loop's fixpoint, its `break`, its `continue` and its re-entry | [`lower::loops`](src/lower/loops.rs) |
| The runs that a computation asks for: inferred, linear and nested | [`lower::runs`](src/lower/runs.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The family reads the lowering only through `Families`, a trait of the base, so the family compiles over the base alone.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
