# gandr-surface-lowering-capability

The capability family of gandr's lowering. It lowers a capability scope and its handlers, a session's endpoints, a method call with its receiver, and a field's access with its assignment. The family compiles over `gandr-surface-lowering-base`, beside the rest of the lowering.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The lowering's capability family. It lowers the capability type, a returner's effect row, the exercise and the perform of an operation, a capability scope with its handlers, and the resumption of a continuation. It lowers a session type, its endpoints and the actions on them. It resolves a method call among the methods in scope, and it lends the receiver at the mode that the method states. It lowers a field's access and its assignment.

**Why.** The lowering is the longest crate in the build of the driver. In a crate of its own, the family type-checks once. An edit of another family then does not type-check it again.

**How.** The family reads the lowering through its host, `F: Families`, a trait of the base. The host holds the lowering's context and answers each call into another family. `gandr-surface-lowering` is the host, and a call from it into this family builds `Capability::new(self)`. Each call is static. A reading of the lowering, such as the minting of a scope, builds `CapabilityRef::new(self)`, which borrows the host and never writes it. The family's tests stay in `gandr-surface-lowering`, because each test lowers a source.

## Provided features

- `Capability`: the family over its host, and each of its entries that the lowering calls ([`lower::capability`](src/lower/capability.rs)).
- `CapabilityRef`: the family's reads over its host, each minting of a scope, an exercise, a session action, a method call or an access among them ([`lower::capability`](src/lower/capability.rs)).
- `mint_capability` and `scope_laws`: a capability value from its authority, and the laws that a scope owes its theory ([`lower::capability`](src/lower/capability.rs)).
- `hold_body`: the body of a method that writes its receiver through, which gives the receiver back ([`lower::method`](src/lower/method.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A host.** A type that implements `Families` of `gandr-surface-lowering-base` holds the context and the other families.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The capability type, the effect row, the exercise, the perform, the scope and the resumption | [`lower::capability`](src/lower/capability.rs) |
| A scope that a model answers | [`lower::capability::answered`](src/lower/capability/answered.rs) |
| A session type, its endpoints and the actions on them | [`lower::session`](src/lower/session.rs) |
| A method call, its receiver mode and the hold of its receiver | [`lower::method`](src/lower/method.rs) |
| A field's access and its assignment | [`lower::access`](src/lower/access.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The family reads the lowering only through `Families`, a trait of the base, so the family compiles over the base alone.
- `vault:01a14daa-a317-7d92-bd17-3f20e87634cd` — background: the theories design — what `with sort x = A` fixes.
- `vault:01a15620-7fbe-7030-a3af-07ffa620eed2` — background: the syntax bikeshed — the row entry's spelling.
- `vault:01a15b47-4304-793b-a542-d12afcf732a6` — anchor: § methods-desugaring — a receiver no hold holds is a value, and an index of one holds it for its read.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
