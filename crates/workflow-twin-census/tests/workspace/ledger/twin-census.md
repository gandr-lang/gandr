# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter | Generic items |
| ----- | ----------------- | ------------- |
| `near` | no | 0 |
| `runtime-emitter` | the emitter | 1 |

Crates under the emitter: 0 of 2.

Generic public items: 1.
