# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

An export carries a function that is not generic, whose operands are fixed-width integers or addresses, and whose result is one of the two. A fixed-width integer is `u8` to `u64`, `i8` to `i64`, `usize` or `isize`. An address is a reference or a raw pointer to a sized type. The column gives the count of such public functions and methods, of the count of all, and its share.

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter | Generic items | Export fragment |
| ----- | ----------------- | ------------- | --------------- |
| `near` | no | 0 | 0 of 0 |
| `runtime-emitter` | the emitter | 1 | 1 of 2 (50 %) |

Crates under the emitter: 0 of 2.

Generic public items: 1.

Public functions in the export fragment: 1 of 2 (50 %).
