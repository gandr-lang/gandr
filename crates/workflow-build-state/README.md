# gandr-workflow-build-state

A Cargo profile directory pruned to the units the recorded builds used, so the build state CI carries from landing to landing stays the size of one build.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-build-state` installs the `build-state` binary. `build-state prune` reads the JSON messages of one or more Cargo builds and removes every unit's files in a profile directory that none of them used.

**Why.** Cargo names a unit's files with a hash of its package, features, profile and dependencies. A dependency, feature or lockfile change writes the unit and everything above it under new hashes and leaves the old ones in place, so a target directory restored and saved on every landing grows by a dependency cone with every manifest change, and every lane pays for the size in transfer, archiving and the caches it evicts.

**How.** A build prints a `compiler-artifact` message for every unit it used, fresh ones included, and a `build-script-executed` message for every build-script output directory. The hashes those paths carry are the keep set. Cargo also copies each executable out under its plain name as a hard link, so the unit behind a plain-named path is the hashed file it shares an inode with. Every hashed entry of `deps`, `build`, `.fingerprint` and `examples` outside the keep set is removed. The [crate docs](src/lib.rs) state the keep set and the refusal of an incomplete account.

## Provided features

- `build-state prune --profile-dir DIR MESSAGES...` prunes `DIR` and prints the entries and mebibytes removed and the entries kept.
- A message file without Cargo's successful `build-finished` message is refused before anything is removed.
- `BuildStateError` names the file behind every refusal.

## Expected features

The message files come from builds into `DIR`, with `--message-format json` (Cargo) or `--cargo-message-format json` (nextest); a file per build, so one prune keeps the units of every build the directory serves. On a platform without inodes, every unit whose name has an executable's stem is kept.

## Examples

```sh
cargo nextest run --workspace --no-run --cargo-message-format json-render-diagnostics > target/units.jsonl
build-state prune --profile-dir target/debug target/units.jsonl
cargo nextest run -p gandr-workflow-build-state
```

## Dependencies

`serde` and `serde_json` read Cargo's messages, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
