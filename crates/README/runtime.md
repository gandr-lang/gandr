# The `runtime` crates

The member rows of the `runtime` category of [`crates/README.md`](../README.md#members): one row for each directory, the directory and what it is.

```text
# Rows sort lexicographically by directory; the dependency order is § Layering.
crates/
├── runtime-emitter/               the L machine's commands copy-and-patched into native code under a content cache, or run on the portable executor
├── runtime-net/                   the network a host holds: streams to peers named by key, chunk fetches and migrations, over iroh
└── runtime-stencils/              the L machine's transitions written once: the stencils the emitter copies and patches, and the portable executor that dispatches them
```
