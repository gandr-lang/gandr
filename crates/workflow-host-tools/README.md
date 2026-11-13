# gandr-workflow-host-tools

Some tools of `mise.toml` publish no binary for the target of a host of ours. A host of another target builds each of them once for each version.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-host-tools` installs the `host-tools` binary. `host-tools build` builds each tool of a target that the table `.config/host-tools/builds.toml` names, at the version `mise.lock` locks, into a directory of keys.

**Why.** mise installs a tool from its release's binary. On the riscv64 host, ten tools of the tree and mise itself publish no binary. There mise holds the binary of another architecture or none, and a job builds the tool from source on the slowest host.

**How.** A fast host cross-builds each such tool. A crate builds with `cargo install`, a cargo package or a Go package from a clone of its tag. A key is the directory `<target>/<install name>/<version>`, where the install name is the tool's directory in mise's install directory. A build takes the lock of its key and builds into a partial directory. At its end, it renames the partial directory into the key. The build keeps a key that stands. The [crate docs](src/lib.rs) state the table, the plan, the steps and the build.

## Provided features

- `host-tools build --target TRIPLE --into DIR --mise-version VERSION` builds each tool of the target whose key does not stand. It prints one line for each tool: `kept`, `built` with its seconds, or `failed` with the refusal.
- A build that fails leaves no key, and its commands' output stays in `DIR/.logs`.
- `HostToolsError` names the tool, the file or the command behind every refusal.

## Expected features

The builder's configuration, `$XDG_CONFIG_HOME/gandr/host-tools.toml`, names the linker and the C tools of each target and the path of each program that a build needs. The tree names no host. The toolchain of the tree holds the target, and `git` and `go` are on the path of a builder of Go tools.

## Examples

```sh
mise run tools:build riscv64gc-unknown-linux-gnu "$XDG_DATA_HOME/gandr/host-tools"
cargo nextest run -p gandr-workflow-host-tools
```

## Dependencies

`serde` and `toml` read the table, the lock and the configuration, and `clap` reads the invocation, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
