# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

`twin-census --write` writes this file from `cargo metadata`. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter |
| ----- | ----------------- |
| `near` | no |
| `runtime-emitter` | the emitter |

Crates under the emitter: 0 of 2.
