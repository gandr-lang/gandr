# gandr-workflow-host-tools

Some tools of `mise.toml` publish no binary for the target of a host of ours. A host of another target builds each of them once for each version, and copies each build to the hosts of that target.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-host-tools` installs the `host-tools` binary. `host-tools build` builds each tool of a target that the table `.config/host-tools/builds.toml` names, at the version `mise.lock` locks, into a directory of keys. `host-tools push` builds the target of each receiver, copies each key to the receivers of its target, and brings mise to the pin on each host.

**Why.** mise installs a tool from its release's binary. On the riscv64 host, ten tools of the tree and mise itself publish no binary. There mise holds the binary of another architecture or none, and a job builds the tool from source on the slowest host.

**How.** A fast host cross-builds each such tool. A crate builds with `cargo install`, a cargo package or a Go package from a clone of its tag. A key is the directory `<target>/<install name>/<version>`, where the install name is the tool's directory in mise's install directory. A build takes the lock of its key and builds into a partial directory. At its end, it renames the partial directory into the key. The build keeps a key that stands. A push copies a key with `rsync` into `installs/<install name>/<version>` on each receiver, as the key's build ends. The key of mise replaces the receiver's mise. A receiver with no mise path, and the builder, take `mise self-update` to the pin. A marker under `DIR/.pushed/<host>/` records each copy and each update that ends, so each goes to a host once. The [crate docs](src/lib.rs) state the table, the plan, the steps, the build and the push.

## Provided features

- `host-tools build --target TRIPLE --into DIR --mise-version VERSION` builds each tool of the target whose key does not stand. It prints one line for each tool: `kept`, `built` with its seconds, or `failed` with the refusal.
- `host-tools push --into DIR --mise-version VERSION` does nothing when the configuration names no receiver. Otherwise it brings the builder's mise to the pin, builds the target of each receiver, and copies each key to the receivers of its target. It prints `pushed`, `updated`, `failed to push` or `failed to update` for each copy and update that runs.
- A build that fails leaves no key, and a copy that fails leaves no marker. The commands' output stays in `DIR/.logs`.
- At the end of each run, the scratch of the builds goes when no build of another run holds it: one target directory and the clones. At rest it holds nothing, and the line `pruned the scratch` reports its removal.
- After a key stands, the keys of the tool's other versions go with their markers, and a line `retired` names each. The builder holds one key for each tool and target.
- `HostToolsError` names the tool, the file or the command behind every refusal.

## Expected features

The builder's configuration, `$XDG_CONFIG_HOME/gandr/host-tools.toml`, names the linker and the C tools of each target, the path of each program that a build needs, and each receiver: its host as ssh names it, its target, and the path of its mise when the builder builds mise for it. The tree names no host. The toolchain of the tree holds the target, and `git` and `go` are on the path of a builder of Go tools. The builder reaches each receiver with `ssh` and `rsync` without a prompt. On the builder, the toolchain follower runs `tools:push` after each fast-forward of `main`.

## Examples

```sh
mise run tools:build riscv64gc-unknown-linux-gnu "$XDG_DATA_HOME/gandr/host-tools"
mise run tools:push
cargo nextest run -p gandr-workflow-host-tools
```

## Dependencies

`serde` and `toml` read the table, the lock and the configuration, and `clap` reads the invocation, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
